From Coq Require Import
     (* Arith.PeanoNat *)
     (* NArith.NArith *)
     Lists.List
     Strings.String.

Import ListNotations.

Open Scope string_scope.

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
  Export Arc.

  Existing Instance Thread.showable_E.

  Definition thread_it {E}
             `{wrapE Thread.E (instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             `{debugE -< E}
             (tid : thread_id_t)
    : itree E (Types.result unit unit) :=
    let it := Thread.denote 1 in
    let it := map_wrap_event_in_it Thread.E (fun iid => (iid, tid)) _ it in
    resum_it _ it.

  Definition denote {E}
             `{wrapE Thread.E (instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             `{debugE -< E}
             (tids : list thread_id_t)
    : itree E unit :=
    let its := List.map (fun tid => (tid, thread_it tid)) tids in
    let it :=
        scheduler
          Nat.eqb
          (fun tid => Ret (Reject tt)) (* spawn *)
          (* TODO: do we want to support spawning of new threads?
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

  Definition initial_state (mem : list (thread_id_t * instruction_id_t * mem_write))
             (entry_locs : list mem_loc)
    : state :=
    {| storage := Storage.initial_state mem;
       threads := List.map
                    (* The first iid is 1; we use iid 0 for reg-writes with initial values *)
                    (Thread.initial_state 1)
                    entry_locs |}.

  Definition handle_thread_E {E}
             `{stateE state -< E}
             `{exceptE disabled -< E}
             `{exceptE Types.error -< E}
             `{debugE -< E}
    : wrapE Thread.E (instruction_id_t * thread_id_t) ~> itree (E) :=
    fun _ e =>
      let '(Wrap e' (iid, tid)) := e in
      let it : itree (storageE
                      +' stateE Thread.state
                      +' exceptE disabled
                      +' exceptE Types.error
                      +' debugE) _ :=
          resum_it _ (Thread.handle_E iid _ e') in
      let it : itree (stateE Thread.state
                      +' stateE Storage.state
                      +' exceptE disabled
                      +' exceptE Types.error
                      +' debugE) _ :=
          (* TODO: is there a better way to do this? I tired using bimap/swap/assoc_r/etc.,
             but couldn't get it to work (also, it didn't look much better). *)
          interp
            (case_ (cat (Storage.handle_storageE iid tid)
                        (case_ (cat inl_ inr_) (* stateE Storage.state *)
                               (case_ (cat inl_ (cat inr_ inr_)) (* exceptE disabled *)
                                      (cat inl_ (cat inr_ (cat inr_ inr_)))))) (* exceptE error *)
                   (case_ inl_ (* stateE Thread.state *)
                          (case_ (cat inl_ (cat inr_ inr_)) (* exceptE disabled *)
                                 (case_ (cat inl_ (cat inr_ (cat inr_ inr_))) (* exceptE error *)
                                        (cat inr_ (cat inr_ (cat inr_ inr_))))))) (* debugE *)
            it in
      'tt <- trigger (Debug ("handle_thread_E: tid '" ++ show tid ++ "'"
                                                     ++ ", iid '" ++ show iid ++ "'"))
      ;; s <- get
      ;; thr_state <- try_unwrap_option (List.nth_error s.(threads) tid)
                                       "get_thread_state: thread is missing"
      ;; let it := run_state it (thr_state : Thread.state) in
         let it := run_state it s.(storage) in
         '(sto_state, (thr_state, ans)) <- resum_it _ it
      ;; let ts := list_replace_nth tid thr_state s.(threads) in
         put (s <| storage := sto_state |> <| threads := ts |>)
      ;; ret ans.

  Definition run {E}
             `{nondetFinE -< E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
             `{debugE -< E}
             (mem : list (thread_id_t * instruction_id_t * mem_write))
             (entry_locs : list mem_loc)
    : itree E (state * unit) :=
    let tids := List.seq 0 (List.length entry_locs) in
    let it := interp (bimap handle_thread_E (id_ _)) (denote tids) in
    run_state (resum_it _ it) (initial_state mem entry_locs).

  Fixpoint exec_helper {R}
           (bound : nat)
           (it : itree (nondetFinE
                        +' exceptE disabled
                        +' exceptE error
                        +' debugE) R)
           (acc : list string)
    : R +
      ((itree (nondetFinE
               +' exceptE disabled
               +' exceptE error
               +' debugE) R) *
       list string) :=
    match bound with
    | 0 => inr (it, ("Bound reached!"::acc))
    | S bound =>
      match observe it with
      | RetF r => inr (it, ("*** RET ***"::acc))
      | TauF it => exec_helper bound it acc (*("Tau"::acc)*)
      | @VisF _ _ _ X o k =>
        match o with
        | inl1 o' =>
          match o' in nondetFinE Y return X = Y -> _ with
          | NondetFin n =>
            fun pf =>
              match Fin.of_nat 0 n with
              | inleft i =>
                let i := eq_rect_r (fun T => T) i pf in
                exec_helper bound (k i) acc
              | _ => inr (it, ("0 is not in [Fin.t n]"::acc))
              end
              (* fold_left (fun acc i => *)
              (*              match acc, Fin.of_nat i n with *)
              (*              | None, inleft i => *)
              (*                let i := eq_rect_r (fun T => T) i pf in *)
              (*                exec_helper bound (k i) *)
              (*              | _, _ => acc *)
              (*              end) *)
              (*           (List.seq 0 n) *)
              (*           None *)
          end eq_refl
        | inr1 (inl1 (Throw (Disabled tt))) => inr (it, ("--disabled--"::acc))
        | inr1 (inr1 (inl1 (Throw (Error msg)))) => inr (it, (msg::acc))
        | inr1 (inr1 (inr1 o')) =>
          match o' in debugE Y return X = Y -> _ with
          | Debug msg => fun pf =>
                          exec_helper bound (k (eq_rect_r (fun T => T) tt pf))
                                      (("debug: " ++ msg)::acc)
          end eq_refl
        end
      end
    end.

  Definition exec n (mem : list (thread_id_t * instruction_id_t * mem_write))
             (entry_locs : list mem_loc)
    : (state * unit) + (_ * list string) :=
    let it := run mem entry_locs in
    exec_helper n it [].
End Make.
