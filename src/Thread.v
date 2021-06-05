From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Lists.ListSet
     (* Strings.String *)
     Morphisms
     Setoid
     RelationClasses .

From ExtLib Require Import
     Structures.Monads
     Data.Monads.ListMonad.
(*      Data.String *)
(*      Structures.Traversable *)
(*      Data.List. *)

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts
     Events.Nondeterminism.

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

From RecordUpdate Require Import RecordSet.

Import ListMonad.
Import ITreeNotations.
Import Monads.
Import MonadNotation.
Import ListNotations.

Require Import
        Types
        Utils.

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.
(* Local Open Scope monad_scope. *)

Definition instruction_id_t := id_t.

Module Denote (Arc : ArcSig).
  Definition mem_read_id_t := id_t.
  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id_t;
                  read_fp : Arc.mem_slc;
                  read_kind : Arc.InsSem.mem_read_kind }.

  Definition mem_write_id_t := id_t.
  Record mem_write : Type :=
    mk_mem_write { write_id : mem_write_id_t;
                   write_fp : Arc.mem_slc;
                   write_kind : Arc.InsSem.mem_read_kind }.


  Variant threadE : Type -> Type :=
  | ThEInsFetch : Arc.InsSem.pc_t -> threadE Arc.InsSem.machine_code
  | ThEInsDecode : Arc.InsSem.machine_code -> threadE Arc.InsSem.ast
  | ThEInsNextLocs : Arc.InsSem.pc_t -> Arc.InsSem.ast ->
                     threadE (list (instruction_id_t * Arc.InsSem.pc_t)).
  (* | ThEInsSem : forall A, Arc.InsSem.E A -> threadE A. *)
  (* Arguments ThEInsSem {A}. *)

  Context {E: Type -> Type}.
  Context `{wrapE threadE instruction_id_t -< E}.
  Context `{wrapE Arc.InsSem.E instruction_id_t -< E}.

  Definition SE := nondet_schedulerE (instruction_id_t * Arc.InsSem.pc_t) +' E.

  (* Definition handle_regE {E} *)
  (*   : wrapE Arc.InsSem.regE instruction_id_t ~> itree E := *)
  (*   fun _ e => *)
  (*     let '(Wrap e iid) := e in *)
  (*     match e with *)
  (*     | Arc.InsSem.RegERead rslc => *)

  (*       Ret (read_reg_slc rslc iid s) *)
  (*     | Arc.InsSem.RegEWrite rslc rval => Ret (write_reg_slc rslc rval iid s, tt) *)
  (*     end. *)

  Definition new_instruction
    : ktree SE (instruction_id_t * Arc.InsSem.pc_t) Types.result :=
    fun '(id, loc) =>
      mem_val <- trigger (Wrap (ThEInsFetch loc) id)
      ;; ast <- trigger (Wrap (ThEInsDecode mem_val) id)
      ;; next_ins <- trigger (Wrap (ThEInsNextLocs loc ast) id)
      ;; ITree.iter (fun next_ins =>
                       match next_ins with
                       | [] => ret (inr tt)
                       | (id, loc)::next_ins => trigger (Spawn (id, loc))
                                              ;; ret (inl next_ins)
                       end) next_ins
      ;; resum_it _ (translate (fun _ e => Wrap e id) (Arc.InsSem.denote ast)
                    ;; ret Accept).

  Definition denote
    : ktree SE (instruction_id_t * Arc.InsSem.pc_t) Types.result :=
    fun '(id, loc) => nondet_scheduler new_instruction [new_instruction (id, loc)].
End Denote.

(*******************************************************************************)

Module State(Arc : ArcSig).
  Module DenoteA := Denote Arc.

  Record mem_reads :=
    mk_mem_reads { mr_footprint : Arc.mem_slc;
                   mr_reads : list DenoteA.mem_read;
                   mr_unsat_slcs : DenoteA.mem_read_id_t -> option (list Arc.mem_slc);
                   mr_reads_from :
                     DenoteA.mem_read_id_t -> option (list (instruction_id_t * DenoteA.mem_write_id_t * Arc.mem_slc)) }.

  Record mem_writes :=
    mk_mem_writes { mw_footprint : Arc.mem_slc;
                    mw_writes : list DenoteA.mem_write;
                    mw_write_val : DenoteA.mem_write_id_t -> option Arc.mem_slc_val;
                    mw_has_propagated : DenoteA.mem_write_id_t -> option bool;
                    mw_committed : bool }.

  Variant instruction_exec_state : Type :=
  (* | IESInitial : instruction_exec_state *)
  | IESFetched : instruction_exec_state
  | IESInstSem : instruction_exec_state
  | IESMemRead : instruction_exec_state
  | IESMemWrite : instruction_exec_state.

  Record fetched_instruction_state :=
    mk_fetched_instruction_state {
        ins_id : instruction_id_t;
        ins_loc : Arc.mem_loc; (*: record fetched address :*)
        (* statically analysed data about the instruction*)
        ins_kind: Arc.instruction_kind;

        (*: The input registers, for ease of dependency calculation :*)
        ins_regs_in : ListSet.set Arc.InsSem.reg_slc;

        (*: The input registers that feed into a memory access address :*)
        ins_regs_feeding_address: ListSet.set Arc.InsSem.reg_slc;
        (*: The output registers, for ease of dependency calculation *)
        ins_regs_out: ListSet.set Arc.InsSem.reg_slc;

        (* dynamic info *)

        (* reg_reads: list (reg * register_read_sources * reg_val); *)

        (* reg_writes: list (reg_name * (list register_write_dependency * register_value)); *)

        ins_mem_reads: option mem_reads;
        ins_mem_writes: option mem_writes;

        ins_finished: bool;

        ins_exec_state: instruction_exec_state }.

  Instance eta_fetched_instruction_state : Settable _ :=
    settable! mk_fetched_instruction_state <ins_id; ins_loc; ins_kind; ins_regs_in; ins_regs_feeding_address; ins_regs_out; ins_mem_reads; ins_mem_writes; ins_finished; ins_exec_state>.

  Definition initial_fetched_instruction_state (loc : Arc.mem_loc)
             (ast : Arc.InsSem.ast)
    : fetched_instruction_state :=
    let '(regs_in, regs_feeding_address, regs_out) := Arc.InsSem.regs_from_ast ast in
    (* instruction_state: *)
    {| ins_id := 0; (* FIXME: get fresh id *)
       ins_loc := loc;
       ins_kind := (Arc.instruction_kind_from_ast ast);
       ins_regs_in := regs_in;
       ins_regs_feeding_address := regs_feeding_address;
       ins_regs_out := regs_out;
       ins_mem_reads := None;
       ins_mem_writes := None;
       ins_finished := false;
       ins_exec_state := IESFetched |}.

  Variant instruction_state :=
  | ISUnfetched : Arc.mem_loc -> instruction_state
  | ISFetched : fetched_instruction_state -> instruction_state.

  Record state :=
    mk_state {
        next_iid : instruction_id_t;
        instruction_tree : tree instruction_state }.

  Instance eta_state : Settable _ :=
    settable! mk_state <next_iid; instruction_tree>.

  Definition initial_state (loc : Arc.mem_loc)
    : state :=
    {| next_iid := 0;
       instruction_tree := Tree (ISUnfetched loc) [] |}.

  Definition read_reg_slc (rslc : Arc.InsSem.reg_slc) (iid : instruction_id_t) (s : state)
    : (state * Arc.InsSem.reg_val) :=
    (* FIXME: *)
    (s, 0%N).

  Definition write_reg_slc (rslc : Arc.InsSem.reg_slc) (val : Arc.InsSem.reg_val)
             (iid : instruction_id_t) (s : state)
    : state :=
    (* FIXME: *)
    s.


  Definition handle_regE {E} : wrapE Arc.InsSem.regE instruction_id_t ~> stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e iid) := e in
      match e with
      | Arc.InsSem.RegERead rslc => Ret (read_reg_slc rslc iid s)
      | Arc.InsSem.RegEWrite rslc rval => Ret (write_reg_slc rslc rval iid s, tt)
      end.

  (* Definition handle_thread {E} : Arc.InsSem.E ~> stateT thread_state (itree E) :=. *)

  (* Definition handle_thread {E} : threadE ~> stateT thread_state (itree E) := *)
  (*   fun _ e thread_state => *)
  (*     match e with *)
  (*     | *)

  (* (* SAZ: I think that all of these [run_foo] functions should be renamed *)
  (*    [interp_foo].  That would be more consistent with the idea that *)
  (*    we define semantics by nested interpretation.  Also, it seems a bit *)
  (*    strange to define [interp_map] in terms of [interp_state]. *)
  (* *) *)
  (* Definition interp_map {E d} : itree (mapE d +' E) ~> stateT map (itree E) := *)
  (*   interp_state (case_ handle_map pure_state). *)

End State.
