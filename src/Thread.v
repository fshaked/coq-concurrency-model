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

Module A.
  Module B.
    Definition a := 0.
  End B.
End A.

Module Thread (Arch : Arch).
  Definition mem_location := nat.
  Record mem_slc : Type :=
    mk_mem_slc { addr : mem_location;
                 size: nat (* in bytes *) }.
  Definition mem_slc_val := nat.

  Definition mem_read_id_t := id_t.
  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id_t;
                  read_fp : mem_slc;
                  read_kind : Arch.InsSem.mem_read_kind }.

  Definition mem_write_id_t := id_t.
  Record mem_write : Type :=
    mk_mem_write { write_id : mem_write_id_t;
                   write_fp : mem_slc;
                   write_kind : Arch.InsSem.mem_read_kind }.

  Definition instruction_id_t := id_t.

  Record mem_reads :=
    mk_mem_reads { mr_footprint : mem_slc;
                   mr_reads : list mem_read;
                   mr_unsat_slcs : mem_read_id_t -> option (list mem_slc);
                   mr_reads_from :
                     mem_read_id_t -> option (list (instruction_id_t * mem_write_id_t * mem_slc)) }.

  Record mem_writes :=
    mk_mem_writes { mw_footprint : mem_slc;
                    mw_writes : list mem_write;
                    mw_write_val : mem_write_id_t -> option mem_slc_val;
                    mw_has_propagated : mem_write_id_t -> option bool;
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
        ins_loc : mem_location; (*: record fetched address :*)
        ins_ast : Arch.InsSem.ast;
        (* statically analysed data about the instruction*)
        ins_kind: Arch.instruction_kind;

        (* ins_initial_semantics_state: instruction_semantics_state; *)
        ins_sem: Arch.InsSem.sem_t;

        (*: The input registers, for ease of dependency calculation :*)
        ins_regs_in : ListSet.set Arch.InsSem.reg_slc;

        (*: The input registers that feed into a memory access address :*)
        ins_regs_feeding_address: ListSet.set Arch.InsSem.reg_slc;
        (*: The output registers, for ease of dependency calculation *)
        ins_regs_out: ListSet.set Arch.InsSem.reg_slc;

        (* dynamic info *)

        (* reg_reads: list (reg * register_read_sources * reg_val); *)

        (* reg_writes: list (reg_name * (list register_write_dependency * register_value)); *)

        ins_mem_reads: option mem_reads;
        ins_mem_writes: option mem_writes;

        ins_finished: bool;

        ins_exec_state: instruction_exec_state }.

  Definition initial_fetched_instruction_state (loc : mem_location)
             (ast : Arch.InsSem.ast)
    : fetched_instruction_state :=
    let '(regs_in, regs_feeding_address, regs_out) := Arch.InsSem.regs_from_ast ast in
    (* instruction_state: *)
    {| ins_id := 0; (* FIXME: get fresh id *)
       ins_loc := loc;
       ins_ast := ast;
       ins_kind := (Arch.instruction_kind_from_ast ast);
       ins_sem := Arch.InsSem.denote ast;
       ins_regs_in := regs_in;
       ins_regs_feeding_address := regs_feeding_address;
       ins_regs_out := regs_out;
       ins_mem_reads := None;
       ins_mem_writes := None;
       ins_finished := false;
       ins_exec_state := IESFetched |}.

  Instance eta_fetched_instruction_state : Settable _ :=
    settable! mk_fetched_instruction_state <ins_id; ins_loc; ins_ast; ins_kind; ins_sem; ins_regs_in; ins_regs_feeding_address; ins_regs_out; ins_mem_reads; ins_mem_writes; ins_finished; ins_exec_state>.

  Variant instruction_state :=
  | ISUnfetched : mem_location -> instruction_state
  | ISFetched : fetched_instruction_state -> instruction_state.

  Definition thread_id_t := id_t.

  Inductive tree (T : Type) : Type :=
  | Tree : T -> list (tree T) -> tree T.
  Arguments Tree {T}.

  Record thread_state :=
    mk_thread_state {
        thr_id : thread_id_t;
        thr_instruction_tree : tree instruction_state }.

  (* Variant ITEThread : Type -> Type := *)
  (* | ITEFetchIns : mem_location -> ITEThread Arch.InsSem.ast. *)

  (* Definition initial_thread_state {E} {HasITEThread : ITEThread -< E} *)
  (*   : ktree E (thread_id_t * mem_location) thread_state := *)
  (*   fun '(id, loc) => *)
  (*     ast <- trigger (ITEFetchIns loc) *)
  (*     ;; let i := initial_instruction_state loc ast in *)
  (*        ret {| thr_id := id; *)
  (*               thr_instruction_tree := Tree i [] |}. *)
  Definition initial_thread_state (id : thread_id_t) (loc : mem_location)
    : thread_state :=
    {| thr_id := id;
       thr_instruction_tree := Tree (ISUnfetched loc) [] |}.

  Definition read_reg_slc (rslc : Arch.InsSem.reg_slc) (i : instruction_state) (s : thread_state)
    : (instruction_state * thread_state * Arch.InsSem.reg_val) :=
    (* FIXME: *)
    (i, s, 0%N).

  Definition write_reg_slc (rslc : Arch.InsSem.reg_slc) (val : Arch.InsSem.reg_val)
             (i : instruction_state) (s : thread_state)
    : (instruction_state *thread_state) :=
    (* FIXME: *)
    (i, s).

  (* Definition lift_reg {E: Type -> Type} *)
  (*   : Arch.InsSem.ITEReg ~> stateT (instruction_state * thread_state) (itree E) := *)
  (*   fun _ e '(i, s) => *)
  (*     match e with *)
  (*     | Arch.InsSem.ITERegRead reg_slc => *)
  (*       Ret (read_reg_slc reg_slc i s) *)
  (*     | Arch.InsSem.ITERegWrite reg_slc val => *)
  (*       Ret (write_reg_slc reg_slc val i s, tt) *)
  (*     end. *)

  Variant ITEThread : Type -> Type :=
  | ITEFetch : mem_location -> ITEThread nat
  | ITEDecode : nat -> ITEThread Arch.InsSem.ast
  | ITENextLocs : mem_location -> Arch.InsSem.ast -> ITEThread (list mem_location).

  (* Definition denote_ins {E : Type -> Type} *)
  (*            {HasITEReg: Arch.InsSem.ITEReg -< E} *)
  (*            {HasITEMem: Arch.InsSem.ITEMem -< E} *)
  (*            {HasITEThread: ITEThread -< E} *)
  (*            (loc : mem_location) *)
  (*   : itree E unit := *)
  (*   mem_val <- trigger (ITEFetch loc) *)
  (*   ;; ast <- trigger (ITEDecode mem_val) *)
  (*   ;; Arch.InsSem.denote ast. *)
    (* ;; let h := bimap lift_reg id_ *)
    (*             (* |> bimap lift_mem *) in *)
    (*    translate h (Arch.InsSem.denote ast). *)
    (* ;; let i := initial_fetched_instruction_state id ast in *)
    (*    i <- ITree.iter *)
    (*          (fun i => match observe i.(ins_sem) with *)
    (*                 | RetF tt => *)
    (*                   (* terminate the iter *) *)
    (*                   trigger (ITEFinish) *)
    (*                   ;; ret (inr (set ins_finished true i)) *)
    (*                 | TauF t => *)
    (*                   trigger (ITEInsSemInternal) *)
    (*                   ;; ret (inl (set ins_sem t i)) *)
    (*                 | VisF e k => *)
    (*                   fmap (fun x => k x) (h _ e) *)
    (*                 end) i *)
    (*    ;; ret tt. *)

  (* Program Fixpoint denote_subtree {E : Type -> Type} *)
  (*         (t : tree instruction_state) *)
  (*   : list (itree E thread_state) := *)
  (*   let '(Tree i ts) := t in *)
  (*   let its := List.concat (List.map denote_subtree ts) in *)
  (*   denote_ins i :: its. *)

  Fixpoint tree_map_with_context {T Y} (f : list T -> T -> list (tree T) -> Y) (pref : list T) (tree: tree T) :=
    let '(Tree x ts) := tree in
    Tree (f pref x ts) (List.map (tree_map_with_context f (x::pref)) ts).


  Variant wrapE {T}: Type -> Type :=
  | Wrap : forall A E, T -> E A -> wrapE A.

  Notation TE := (nondet_finE +' ITEThread +' Arch.InsSem.E).

  CoFixpoint nondet_scheduler {S}
             (spawn : ktree TE S (itree TE unit * list S))
             (q : list S)
             (its : list (itree TE unit))
    : itree TE unit :=
    match (q, its) with
    | ([], []) => Ret tt
    | _ =>
      n <- trigger (NondetFin (List.length q + List.length its))
      ;; match List.nth_error q n with
         | Some s =>
           '(it, ss) <- spawn s
           ;; Tau (nondet_scheduler spawn (ss ++ list_remove_nth n q) (it::its))
         | None =>
           let n := n - List.length q in
           match List.nth_error its n with
           | Some it =>
             match observe it with
             | RetF _ => Tau (nondet_scheduler spawn q (list_remove_nth n its))
             | TauF it => Tau (nondet_scheduler spawn q (list_replace_nth n it its))
             (* | @VisF _ _ _ X (inr1 (inl1 (ITENextLocs loc ast))) k => *)
             (*   Vis (inr1 (inl1 (ITENextLocs loc ast))) *)
             (*       (fun next_locs => *)
             (*          nondet_scheduler spawn (List.map spawn next_locs ++ *)
             (*                                           list_replace_nth n (k next_locs) its)) *)
             | @VisF _ _ _ X o k =>
               Vis o (fun x => nondet_scheduler spawn q (list_replace_nth n (k x) its))
             end
           | None => ITree.spin (* catch fire *)
           end
         end
    end.

  Definition new_instruction : ktree TE mem_location (itree TE unit * list mem_location) :=
    fun loc =>
      mem_val <- trigger (ITEFetch loc)
      ;; ast <- trigger (ITEDecode mem_val)
      ;; next_locs <- trigger (ITENextLocs loc ast)
      ;; let it :=
             (* interp id_ (Arch.InsSem.denote ast) in *)
             translate inr1 (translate inr1 (Arch.InsSem.denote ast)) in
         ret (it, next_locs).

  Definition denote (loc : mem_location) : itree TE unit :=
    nondet_scheduler new_instruction [loc] [].

















  Definition handle_ITEReg {E : Type -> Type} {HasITEReg : ITEReg -< E}
             (t : thread_state) (i : instruction_state)
    : ITEReg ~> itree E :=
    fun _ e =>
      match e with
      | ITERegRead r =>
        v <- trigger (ITERegRead r)
        ;; record_reg_read r v (* on instruction_state *)
        ;; ret v
      | ITERegWrite r v =>
        record_ref_write r v (* on instruction_state *)
        trigger (ITERegWrite r v)
      end.

    Definition handle_ITEMem {E : Type -> Type} {HasITEMem : ITEMem -< E} : ITEMem ~> itree E :=
    fun _ e =>
      match e with
      | ITEMemRead l =>
        record_pending_mem_read l (* on instruction_state *)
        ;; v <- trigger (ITEMemRead l)
        ;; ret v
      | ITEMemWrite : mem_location -> nat -> ITEMem unit.

  Fixpoint denote_instruction {E} {HasITEIns : ITEIns -< E} (i : instruction_state)
    : itree E instruction_state :=
    interp handle_ins_sem (InsSem_denote i.(ins_ast))

End Thread.

Section Thread.
  (* Register name indexed by its bit-size *)
  Variable reg : Type.
  Variable reg_size : reg -> nat.
  (* `(a,b)` represents all the bits between `a` and `b`, including `a` but not
  including `b`. *)
  Definition reg_slc : Type := reg * nat * nat.
  Definition reg_val (r : reg) : Type := Bvector (reg_size r).


  Variant ITEReg : Type -> Type :=
  (* Invariant: the answer is a `reg_val r`, but only the bits that correspond
  to `slc` are meaningful, the rest will be ignored. *)
  | ITERegRead (r : reg) : reg_slc -> ITEReg (reg_val r)
  | ITERegWrite (r : reg) : reg_slc -> reg_val r -> ITEReg unit.

  Variable mem_location : Type.

  Record mem_slc : Type :=
    mk_mem_slc { addr : mem_location;
                 size: nat (* in bytes *) }.
  Definition mem_slc_val := nat.

  Variable mem_read_kind : Type.
  Definition mem_read_id_t := nat.
  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id_t;
                  read_fp : mem_slc;
                  read_kind : mem_read_kind }.

  Variable mem_write_kind : Type.
  Definition mem_write_id_t := nat.
  Record mem_write : Type :=
    mk_mem_write { write_id : mem_write_id_t;
                   write_fp : mem_slc;
                   write_kind : mem_read_kind }.

  Definition instruction_id_t := nat.

  Record mem_reads :=
    mk_mem_reads { mr_footprint : mem_slc;
                   mr_reads : list mem_read;
                   mr_unsat_slcs : mem_read_id_t -> option (list mem_slc);
                   mr_reads_from :
                     mem_read_id_t -> option (list (instruction_id_t * mem_write_id_t * mem_slc)) }.

  Record mem_writes :=
    mk_mem_writes { mw_footprint : mem_slc;
                    mw_writes : list mem_write;
                    mw_write_val : mem_write_id_t -> option mem_slc_val;
                    mw_has_propagated : mem_write_id_t -> option bool;
                    mw_committed : bool }.

  Variable instruction_ast : Type.
  Variable instruction_kind : Type.
  Variable instruction_semantics_state : Type.

  Variant instruction_exec_state : Type :=
  (* | IESInitial : instruction_exec_state *)
  | IESFetched : instruction_exec_state
  | IESInstSem : instruction_exec_state
  | IESMemRead : instruction_exec_state
  | IESMemWrite : instruction_exec_state.

  Record instruction_state :=
    mk_instruction_state {
        ins_id : instruction_id_t;
        ins_loc : mem_location; (*: record fetched address :*)
        ins_ast : instruction_ast;
        (* statically analysed data about the instruction*)
        ins_kind: instruction_kind;

        (* ins_initial_semantics_state: instruction_semantics_state; *)

        (*: The input registers, for ease of dependency calculation :*)
        ins_regs_in : ListSet.set reg_slc;

        (*: The input registers that feed into a memory access address :*)
        ins_regs_feeding_address: ListSet.set reg_slc;
        (*: The output registers, for ease of dependency calculation *)
        ins_regs_out: ListSet.set reg_slc;

        (* dynamic info *)

        (* reg_reads: list (reg * register_read_sources * reg_val); *)

        (* reg_writes: list (reg_name * (list register_write_dependency * register_value)); *)

        ins_mem_reads: option mem_reads;
        ins_mem_writes: option mem_writes;

        ins_finished: bool;

        ins_exec_state: instruction_exec_state }.

  Variant ITEIns : Type -> Type :=
  | ITEInsFetch : mem_location -> ITEIns instruction_state.
  (* | ITEInsSem : . *)

  Context {InsSem_E : Type -> Type}.
  (* Context {InsSem_HasITEReg : ITEReg -< InsSem_E} {HasITEMem : ITEMem -< InsSem_E}. *)

  Variable InsSem_denote : instruction_ast -> itree InsSem_E unit.

  Definition handle_ins_sem .. := .
    match i.(ins_exec_state) with
    | IESFetched =>
      InsSem_denote i.(ins_ast)
                        trigger (ITEInsFetch next_instructions)

  Fixpoint denote_instruction {E} {HasITEIns : ITEIns -< E} (i : instruction_state)
    : itree E instruction_state :=
    interp handle_ins_sem (InsSem_denote i.(ins_ast))


  Variable fetch_instruction : mem_location -> instruction_ast.
  Variable regs_from_ast : instruction_ast ->
                           (ListSet.set reg_slc * ListSet.set reg_slc * ListSet.set reg_slc).
  Variable instruction_kind_from_ast : instruction_ast -> instruction_kind.

  Definition handle_ITEIns {E : Type -> Type} : ITEIns ~> itree E :=
    fun _ e =>
      match e with
      | ITEInsFetch loc =>
        let ast := fetch_instruction loc in
        let '(regs_in, regs_feeding_address, regs_out) := regs_from_ast ast in
        ret
          (* instruction_state: *)
          {| ins_id := 0; (* FIXME: get fresh id *)
             ins_loc := loc;
             ins_ast := ast;
             ins_kind := (instruction_kind_from_ast ast);
             ins_regs_in := regs_in;
             ins_regs_feeding_address := regs_feeding_address;
             ins_regs_out := regs_out;
             ins_mem_reads := None;
             ins_mem_writes := None;
             ins_finished := false;
             ins_exec_state := IESFetched |}
      end.
    
  (* Definition denote_inst (i : instruction_state) : itree E unit := *)
  (*   match i.(ins_semantics_state) with *)
  (*   | IESInitial => *)
  (*   end. *)

  Definition thread_id_t := nat.

  Inductive tree (T : Type) : Type :=
  | T : T -> list (tree T) -> tree T.

  Record thread_state :=
    mk_thread_state {
        thr_id : thread_id_t;
        thr_instruction_tree : tree instruction_state; }.

  Variant ITEMem : Type -> Type :=
  | ITEMemRead : mem_read -> ITEMem mem_slc_val
  | ITEMemWrite : mem_write -> mem_slc_val -> ITEMem unit.

  (* Context {E : Type -> Type}. *)
  (* Context {HasITEMem : ITEMem -< E}. *)
End Thread.
