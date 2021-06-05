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
Import RecordSetNotations.

Require Import Utils.
Require Import Types.
Require Import Thread.
Require Import Storage.

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.

(* Local Open Scope monad_scope. *)

Module System (Arc : ArcSig).
  Module ThrDenote := Thread.Denote Arc.
  Definition thread_id_t := Utils.id_t.

  Definition denote {E}
             `{wrapE ThrDenote.SE thread_id_t -< E}
             (entry_locs : list nat)
    : itree (nondet_schedulerE unit +' E) unit :=
    List.length entry_locs
    $> List.seq 0
    $> List.combine entry_locs
    $> List.map (fun '(eloc, tid) => wrap_it tid _ (ThrDenote.denote (0, eloc)))
    $> nondet_scheduler (fun tt => ITree.spin).
       (* The spin is unreachable.
          TODO: do we want to support spawning of new threads?
          Probably not. *)




  Module ThrState := Thread.State Arc.
  Module StoState := Storage.State Arc.

  Record state :=
    mk_state {
        storage : StoState.state;
        (* thread-tid is in index tid *)
        threads : list ThrState.state }.

  Instance eta_state : Settable _ :=
    settable! mk_state <storage; threads>.

  Definition initial_state (mem : Arc.mem_loc -> option Arc.mem_slc_val) (entry_locs : list Arc.mem_loc)
    : state :=
    {| storage := StoState.initial_state mem;
       threads := List.map ThrState.initial_state entry_locs |}.

  Definition handle_thr_regE {E}
    : wrapE (wrapE Arc.InsSem.regE Thread.instruction_id_t) thread_id_t ~> stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e tid) := e in
      match List.nth_error s.(threads) tid with
      | Some thr_state =>
        '(thr_state, a) <- ThrState.handle_regE _ e thr_state
        ;; let ts := list_replace_nth tid thr_state s.(threads) in
           Ret (s <| threads := ts |>, a)
      | None => ITree.spin (* Unreachable *)
      end.

  Definition handle_thr_memE {E}
    : wrapE (wrapE Arc.InsSem.memE Thread.instruction_id_t) thread_id_t ~> stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e tid) := e in
      match List.nth_error s.(threads) tid with
      | Some thr_state =>
        '(thr_state, a) <- ThrState.handle_memE _ e thr_state
        ;; let ts := list_replace_nth tid thr_state s.(threads) in
           Ret (s <| threads := ts |>, a)
      | None => ITree.spin (* Unreachable *)
      end.

  Definition handle_threadE {E}
    : wrapE (wrapE ThrDenote.threadE Thread.instruction_id_t) thread_id_t ~> stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e tid) := e in
      match List.nth_error s.(threads) tid with
      | Some thr_state =>
        let '(Wrap e iid) := e in
        match e with
        | ThEFetch loc => Ret(s, 0%N) (* FIXME: *)
        | ThEDecode code => Ret(s, Arc.InsSem.decode code)
        | ThENextLocs loc ast =>
          let next_pcs := Arc.InsSem.next_pc loc ast in
          let iids := List.seq thr_state.(next_iid) (List.length next_pcs) in
          let thr_state := thr_state <| next_iid := thr_state.(next_iid) + (List.length next_pcs) |> in
          let ts := list_replace_nth tid thr_state s.(threads) in
          Rest(s <| thread := ts |>, list.compose iids next_pcs)
        end
      | None => ITree.spin (* Unreachable *)
      end.








      Definition interp_system {E}
                 (it : itree (systemE +' E) unit)
        : system_state -> itree E (system_state * unit) :=
        let h := bimap h_reg (bimap h_memory (id_ _)) in
        let it := interp h it in
        fun s => interp_map (interp_map t' regs) mem.


      (** We can then define an evaluator for closed assembly programs by interpreting
    both store and heap events into two instances of [mapE], and running them
    both in the empty initial environments.  *)
      Definition run_system (mem : nat -> option nat) (entry_locs : list nat) :=
        interp_system (denote entry_locs) (initial_state mem entry_locs).
