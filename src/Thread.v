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

  Variant ITEThread : Type -> Type :=
  | ITEFetch : mem_location -> ITEThread nat
  | ITEDecode : nat -> ITEThread Arch.InsSem.ast
  | ITENextLocs : mem_location -> Arch.InsSem.ast -> ITEThread (list mem_location).

  Definition new_instruction {E} `{ITEThread -< E} `{Arch.InsSem.E -< E}
    : ktree (nondet_schedulerE mem_location +' E) mem_location unit :=
    fun loc =>
      mem_val <- trigger (ITEFetch loc)
      ;; ast <- trigger (ITEDecode mem_val)
      ;; next_locs <- trigger (ITENextLocs loc ast)
      ;; ITree.iter (fun locs =>
                       match locs with
                       | [] => ret (inr tt)
                       | l::locs => trigger (Spawn l)
                                  ;; ret (inl locs)
                       end) next_locs
      ;; resum_it unit (Arch.InsSem.denote ast).

  Definition denote {E} `{ITEThread -< E} `{Arch.InsSem.E -< E}
    : ktree (nondet_schedulerE mem_location +' E) mem_location unit :=
    fun loc => nondet_scheduler new_instruction [new_instruction loc].






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

  Record thread_state :=
    mk_thread_state {
        thr_id : thread_id_t;
        thr_instruction_tree : tree instruction_state }.

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
End Thread.
