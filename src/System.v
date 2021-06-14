From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Lists.ListSet
     Strings.String
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
     Events.Exception
     Events.State.

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Import ListMonad.
Import ITreeNotations.
Import Monads.
Import MonadNotation.
Import ListNotations.
Import RecordSetNotations.

Require Import Utils Types Thread Storage.

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.

(* Local Open Scope monad_scope. *)

Module Make (Arc : ArcSig).
  Module Thread := Thread.Make Arc.
  Module Storage := Storage.Make Arc.

  Definition thread_it {E}
             `{wrapE Thread.threadE (instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             (tid : thread_id_t)
    : itree E (Types.result unit unit) :=
    (* TODO: convert loc from nat to Arc.InsSem.pc_t *)
    let it := Thread.denote 0 in
    let it := map_wrap_event_in_it Thread.threadE (fun iid => (iid, tid)) _ it in
    resum_it _ it.

  Definition denote {E}
             `{wrapE Thread.threadE (instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             (tids : list thread_id_t)
    : itree E unit :=
    let its := List.map (fun tid => (tid, thread_it tid)) tids in
    let it :=
        scheduler
          Nat.eqb
          (fun tid => ITree.spin) (* spawn *)
             (* The spin is unreachable.
                TODO:   do we want to support spawning of new threads?
                Probably not. *)
          (fun 'tt _ => tt) (* fold_results *)
          tt its None in
    resum_it _ it.

  Record state :=
    mk_state { storage : Storage.state;
               (* thread-tid is in index tid *)
               threads : list Thread.state }.

  Instance eta_state : Settable _ :=
    settable! mk_state <storage; threads>.

  Definition initial_state (mem : list (thread_id_t * instruction_id_t * Arc.mem_write))
             (entry_locs : list mem_loc)
    : state :=
    {| storage := Storage.initial_state mem;
       threads := List.map (Thread.initial_state 0)  entry_locs |}.

  Definition handle_storageE {E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
    : wrapE Thread.storageE (instruction_id_t * thread_id_t) ~>
            stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e (iid, tid)) := e in
      match e with
      | Thread.StEReadInstruction pc => Ret (s, ({| location := pc; size := 4 |}, []))
      | Thread.StERead read uslcs => Ret (s, [])
      | Thread.StEWrite write => Ret (s, tt)
      end.

  Definition handle_threadE {E}
             `{wrapE Thread.storageE (instruction_id_t * thread_id_t) -< E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
    : wrapE Thread.threadE (instruction_id_t * thread_id_t) ~>
            stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e (iid, tid)) := e in
      Thread.handle_threadE iid _ e thr_state


      thr_state <- try_unwrap_option (List.nth_error s.(threads) tid)
                                    "get_thread_state: thread is missing"
      ;; let it := Thread.handle_threadE iid _ e thr_state in
         (* FIXME: how does the storage state change propagate? *)
         '(thr_state, answer) <- resum_it _ (wrap_event_in_it Thread.storageE (iid, tid) _ it)
      ;; let ts := list_replace_nth tid thr_state s.(threads) in
         ret (s <| threads := ts |>, answer).

  Definition interp_system {E}
    : itree (wrapE Thread.threadE (Thread.instruction_id_t * thread_id_t) +' E) ~>
            stateT state (itree E) :=
    let h := cat handle_threadE handle_storageE in
    interp_state (case_ h pure_state).

  Definition run_system (mem : list (thread_id_t * instruction_id_t * Arc.mem_write)) (entry_locs : list Arc.InsSem.pc_t) :=
    let tids := List.seq 0 (List.length entry_locs) in
    interp_system (denote tids) (initial_state mem entry_locs).
End Make.
