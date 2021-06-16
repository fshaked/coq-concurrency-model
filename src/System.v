From Coq Require Import
     (* Arith.PeanoNat *)
     (* NArith.NArith *)
     Lists.List
     Strings.String.

Import ListNotations.

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
     Events.State.

Import Monads.
Import ITreeNotations.

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Utils Types.

Module Make (Arc : ArcSig)
       (Thread : ThreadSig Arc)
       (Storage : StorageSig Arc).

  Definition thread_it {E}
             `{wrapE Thread.E (instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             (tid : thread_id_t)
    : itree E (Types.result unit unit) :=
    let it := Thread.denote 0 in
    let it := map_wrap_event_in_it Thread.E (fun iid => (iid, tid)) _ it in
    resum_it _ it.

  Definition denote {E}
             `{wrapE Thread.E (instruction_id_t * thread_id_t) -< E}
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
       threads := List.map (Thread.initial_state 0) entry_locs |}.

  Definition interp_storage {E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
             (iid : instruction_id_t) (tid : thread_id_t)
    : itree (Arc.storageE +' E) ~> stateT Storage.state (itree E) :=
    interp_state (case_ (Storage.handle_storageE iid tid) pure_state).

  Definition handle_thread_E {E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
             `{stateE state -< E}
    : wrapE Thread.E (instruction_id_t * thread_id_t) ~> itree E :=
    fun _ e =>
      let '(Wrap e (iid, tid)) := e in
      s <- get
      ;; thr_state <- try_unwrap_option (List.nth_error s.(threads) tid)
                                       "get_thread_state: thread is missing"
      ;; let it : itree _ (Thread.state * _) := Thread.handle_E iid _ e thr_state in
         '(sto_state, (thr_state, ans)) <- interp_storage iid tid _ it s.(storage)
      ;; let ts := list_replace_nth tid thr_state s.(threads) in
         put (s <| storage := sto_state |> <| threads := ts |>)
      ;; ret ans.

  Definition handle_disabled {E}
    : exceptE disabled ~> itree E :=
    fun _ e =>
      let '(Throw Disabled) := e in
      (* FIXME: *)
      ITree.spin.

  Definition handle_error {E}
    : exceptE error ~> itree E :=
    fun _ e =>
      let '(Throw (Error msg)) := e in
      (* FIXME: *)
      ITree.spin.

  Definition interp_system {E}
    : itree (wrapE Thread.E (instruction_id_t * thread_id_t)
             +' exceptE disabled
             +' exceptE error
             +' E) ~>
            stateT state (itree E) :=
    fun _ it =>
      let it := interp (bimap  handle_thread_E
                               (id_ (exceptE disabled +' exceptE error +' E)))
                       it in
      let it : itree (stateE state +' exceptE disabled +' exceptE error +' E) _ :=
          resum_it _ it in
      let it : itree (stateE state +' E) _ :=
          interp (bimap (id_ (stateE state))
                        (case_ handle_disabled
                               (case_ handle_error (id_ E)))) it in
      run_state it.

  Definition run {E}
             `{nondetFinE -< E}
             (mem : list (thread_id_t * instruction_id_t * Arc.mem_write))
             (entry_locs : list mem_loc)
    : itree E (state * unit) :=
    let tids := List.seq 0 (List.length entry_locs) in
    interp_system _ (denote tids) (initial_state mem entry_locs).
End Make.
