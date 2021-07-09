From Coq Require Import
     (* Arith.PeanoNat *)
     (* NArith.NArith *)
     Lists.List
     Strings.String.

Import ListNotations.

Open Scope string_scope.

From ExtLib Require Import
     Core.RelDec.

From ITree Require Import
     Events.Exception
     Events.State
     ITree
     ITreeFacts.

Import Monads.
Import ITreeNotations.

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 9.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Utils Types.
Require Import  Decision.

Module Make (Arc : ArcSig)
       (Thread : ThreadSig Arc)
       (Storage : StorageSig Arc).
  Export Arc.

  Existing Instance Thread.showable_E.
  Existing Instance Thread.showable_state.
  Existing Instance Storage.showable_state.

  Definition thread_it {E}
             `{chooseE (instruction_id * bool) -< E}
             `{wrapE Thread.E (instruction_id * thread_id) -< E}
             `{chooseE mem_read_id -< E}
             `{chooseE mem_write_id -< E}
             `{chooseE nat -< E}
             `{exceptE error -< E}
             `{debugE -< E}
             (tid : thread_id)
    : itree E (Types.result unit unit) :=
    let it := Thread.denote (InstructionID 1) in
    let it := map_wrap_event_in_it Thread.E (fun iid => (iid, tid)) _ it in
    resum_it _ it.

  Definition is_eager {R} : itree (schedulerE thread_id
                                   +' chooseE (instruction_id * bool)
                                   +' wrapE Thread.E (instruction_id * thread_id)
                                   +' chooseE mem_read_id
                                   +' chooseE mem_write_id
                                   +' chooseE nat
                                   +' exceptE error
                                   +' debugE) R
                              -> bool :=
      fun it =>
        match observe it with
        | RetF _ => true
        | TauF _ => true
        | @VisF _ _ _ X o k =>
          match o with
          | inl1 e' => true (* schedulerE thread_id *)
          | inr1 (inl1 _) => true (* chooseE (instruction_id * bool) *)
          | inr1 (inr1 e') => Thread.is_eager_event _ _ e'
          end
        end.

  Instance RelDec_thread_id : RelDec (@eq thread_id) :=
    { rel_dec := fun i1 i2 => isTrue (i1 = i2) }.

  Instance RelDec_thread_id_Correct: RelDec_Correct RelDec_thread_id.
  Proof.
    constructor. intros x y.
    unfold rel_dec. simpl.
    unfold isTrue. destruct decide; split; auto.
    intros. discriminate.
  Qed.

  Definition denote {E}
             `{chooseE (thread_id * bool) -< E}
             `{chooseE (instruction_id * bool) -< E}
             `{wrapE Thread.E (instruction_id * thread_id) -< E}
             `{chooseE mem_read_id -< E}
             `{chooseE mem_write_id -< E}
             `{chooseE nat -< E}
             `{exceptE error -< E}
             `{debugE -< E}
             (tids : list thread_id)
    : itree E unit :=
    let its := List.map (fun tid => (tid, thread_it tid)) tids in
    let it := scheduler (fun tid => Ret (Reject tt)) (* spawn *)
                        (* TODO: do we want to support spawning of new threads? *)
                        (*       Probably not. *)
                        is_eager
                        (fun 'tt _ => tt) (* fold_results *)
                        tt its None in
    resum_it _ it.

  Record state :=
    mk_state { storage : Storage.state;
               (* thread-tid is in index tid *)
               threads : list Thread.state }.

  Instance eta_state : Settable _ :=
    settable! mk_state <storage; threads>.

  Local Open Scope string_scope.
  Instance showable_state : Showable state :=
    { show :=
        fun s =>
          "-- Storage ------------------------------------------------" ++ newline ++
          show s.(storage) ++ newline ++
          String.concat ""
            (List.map (fun '(tid, t) =>
                         "-- Thread " ++ show tid ++ " ------------------------------------------------" ++ newline ++ show t)
                      (List.combine (List.seq 0 (List.length s.(threads))) s.(threads)))
    }.
  Close Scope string_scope.

  Definition initial_state (mem : list (thread_id * instruction_id * mem_write))
             (entry_locs : list mem_loc)
    : state :=
    {| storage := Storage.initial_state mem;
       threads := List.map
                    (* The first iid is 1; we use iid 0 for reg-writes with initial values *)
                    (Thread.initial_state (InstructionID 1))
                    entry_locs |}.

  Definition handle_thread_E
             (* {E} *)
             (* `{stateE state -< E} *)
             (* `{exceptE disabled -< E} *)
             (* `{exceptE Types.error -< E} *)
             (* `{debugE -< E} *)
    : wrapE Thread.E (instruction_id * thread_id) ~>
            itree (stateE state
                   +' exceptE disabled
                   +' exceptE Types.error
                   +' debugE) :=
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
      'tt <- trigger (Debug ("handle_thread_E: tid " ++ show tid
                                                    ++ ", iid " ++ show iid))
      ;; s <- get
      ;; let '(ThreadID tidn) := tid in
         thr_state <- try_unwrap_option (List.nth_error s.(threads) tidn)
                                       "get_thread_state: thread is missing"
      ;; let it := run_state it (thr_state : Thread.state) in
         let it := run_state it s.(storage) in
         '(sto_state, (thr_state, ans)) <- resum_it _ it
      ;; let ts := list_replace_nth tidn thr_state s.(threads) in
         put (s <| storage := sto_state |> <| threads := ts |>)
      ;; ret ans.

  Notation systemE := (chooseE (thread_id * bool)
                       +' chooseE (instruction_id * bool)
                       +' chooseE mem_read_id
                       +' chooseE mem_write_id
                       +' chooseE nat
                       +' exceptE disabled
                       +' exceptE error
                       +' debugE)%type.

  Definition run
             (* {E} *)
             (* `{chooseE (thread_id * bool) -< E} *)
             (* `{chooseE (instruction_id * bool) -< E} *)
             (* `{chooseE mem_read_id -< E} *)
             (* `{chooseE mem_write_id -< E} *)
             (* `{chooseE nat -< E} *)
             (* `{exceptE disabled -< E} *)
             (* `{exceptE error -< E} *)
             (* `{debugE -< E} *)
             (mem : list (thread_id * instruction_id * mem_write))
             (entry_locs : list mem_loc)
    : itree systemE (state * unit) :=
    let tids := List.map ThreadID (List.seq 0 (List.length entry_locs)) in
    let it
        : itree
            (chooseE (thread_id * bool) +' chooseE (instruction_id * bool)
             +' wrapE Thread.E (instruction_id * thread_id)
             +' chooseE mem_read_id +' chooseE mem_write_id +' chooseE nat
             +' exceptE error +' debugE) unit
        := denote tids in
    let it : itree
               (stateE state
                +' chooseE (thread_id * bool) +' chooseE (instruction_id * bool)
                +' chooseE mem_read_id +' chooseE mem_write_id +' chooseE nat
                +' exceptE disabled +' exceptE error +' debugE) unit
        := interp (case_ (cat inl_ inr_) (* chooseE (thread_id * bool) *)
                         (case_ (cat inl_ (cat inr_ inr_)) (* chooseE (instruction_id * bool) *)
                                     (case_ (cat handle_thread_E (* wrapE Thread.E (instruction_id * thread_id) *)
                                                 (case_ inl_ (* stateE state *)
                                                        (case_ (cat inl_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ inr_)))))) (* exceptE disabled *)
                                                               (case_ (cat inl_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ inr_))))))) (* exceptE error *)
                                                                      (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ inr_))))))))))) (* debugE *)
                                            (case_ (cat inl_ (cat inr_ (cat inr_ inr_))) (* chooseE mem_read_id *)
                                                   (case_ (cat inl_ (cat inr_ (cat inr_ (cat inr_ inr_)))) (* chooseE mem_write_id *)
                                                          (case_ (cat inl_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ inr_))))) (* chooseE nat *)
                                                                 (case_ (cat inl_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ inr_))))))) (* exceptE error *)
                                                                        (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ (cat inr_ inr_)))))))))))))) (* debugE *)
                  it in
    run_state it (initial_state mem entry_locs).

  Section Step.
    Notation R := (state * unit)%type.

    Variant step_result :=
    | SNondet : list (itree systemE R * bool) -> step_result
    | SNext : option string -> itree systemE R -> step_result
    | SAccept : R -> step_result
    | SReject : step_result
    | SError : string -> step_result.

    Definition step (it : itree systemE R) : step_result :=
      match observe it with
      | RetF r => SAccept r
      | TauF it => SNext None it
      | @VisF _ _ _ X o k =>
        match o with
        | inl1 o' => (* chooseE (thread_id * bool) *)
          match o' in chooseE _ Y return X = Y -> _ with
          | Choose l =>
            fun pf =>
              SNondet (List.map (fun '(tid, eager) =>
                                   let i := eq_rect_r (fun T => T) (tid, eager) pf in
                                   (k i, eager))
                                l)
          end eq_refl
        | inr1 (inl1 o') => (* chooseE (instruction_id * bool) *)
          match o' in chooseE _ Y return X = Y -> _ with
          | Choose l =>
            fun pf =>
              SNondet (List.map (fun '(iid, eager) =>
                                   let i := eq_rect_r (fun T => T) (iid, eager) pf in
                                   (k i, eager))
                                l)
          end eq_refl
        | inr1 (inr1 (inl1 o')) => (* chooseE mem_read_id *)
          match o' in chooseE _ Y return X = Y -> _ with
          | Choose l =>
            fun pf =>
              SNondet (List.map (fun rid =>
                                   let i := eq_rect_r (fun T => T) rid pf in
                                   (k i, false))
                                l)
          end eq_refl
        | inr1 (inr1 (inr1 (inl1 o'))) => (* chooseE mem_write_id *)
          match o' in chooseE _ Y return X = Y -> _ with
          | Choose l =>
            fun pf =>
              SNondet (List.map (fun wid =>
                                   let i := eq_rect_r (fun T => T) wid pf in
                                   (k i, false))
                                l)
          end eq_refl
        | inr1 (inr1 (inr1 (inr1 (inl1 o')))) => (* chooseE nat *)
          match o' in chooseE _ Y return X = Y -> _ with
          | Choose l =>
            fun pf =>
              SNondet (List.map (fun n =>
                                   let i := eq_rect_r (fun T => T) n pf in
                                   (k i, false))
                                l)
          end eq_refl
        | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (Throw (Disabled tt))))))) => SReject
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (Throw (Error msg)))))))) => SError msg
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 o')))))) =>
          match o' in debugE Y return X = Y -> _ with
          | Debug msg => fun pf => SNext (Some msg) (k (eq_rect_r (fun T => T) tt pf))
          end eq_refl
        end
      end.
  End Step.
End Make.
