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
  Existing Instance Thread.showable_state.
  Existing Instance Storage.showable_state.

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


  Section Execute.
    Notation execE := (nondetFinE +' exceptE disabled +' exceptE error
                       +' debugE)%type.

    Notation R := (state * unit)%type.
    Variant exec_result :=
    | ERReturn : R -> exec_result
    | ERBound : exec_result
    | ERDisabled : exec_result
    | ERError : string -> exec_result.

    Definition nondet_callback := forall n:nat, (Fin.t n -> exec_result) -> exec_result.
    Variable ncall : nondet_callback.

    Definition debug_callback := string -> (unit -> exec_result) -> exec_result.
    Variable dcall : debug_callback.

    Fixpoint exec_helper (bound : nat) (it : itree execE R) : exec_result :=
      match bound with
      | 0 => ERBound
      | S bound =>
        match observe it with
        | RetF r => ERReturn r
        | TauF it => exec_helper bound it
        | @VisF _ _ _ X o k =>
          match o with
          | inl1 o' =>
            match o' in nondetFinE Y return X = Y -> _ with
            | NondetFin n =>
              fun pf => ncall n (fun i =>
                                let i := eq_rect_r (fun T => T) i pf in
                                exec_helper bound (k i))
                      (*    match Fin.of_nat i n with *)
                      (*    | inleft i => *)
                      (*      let i := eq_rect_r (fun T => T) i pf in *)
                      (*      exec_helper bound (k i) *)
                      (*    | _ => ERError "exec_helper: " ++ show i ++ " is not in the range [0," ++ show n ++ ")" *)
                      (*    end) *)
                      (* n *)
                (* match fold_left (fun 'res i => *)
                (*                    match res, Fin.of_nat i n with *)
                (*                    | None, inleft i => *)
                (*                      let i := eq_rect_r (fun T => T) i pf in *)
                (*                      match exec_helper bound (k i) with *)
                (*                      | ERDisabled => None *)
                (*                      | res => Some res *)
                (*                      end *)
                (*                    | _, _ => res *)
                (*                    end) *)
                (*                 (List.seq 0 n) *)
                (*                 None with *)
                (* | Some res => res *)
                (* | None => ERDisabled *)
                (* end *)
            end eq_refl
          | inr1 (inl1 (Throw (Disabled tt))) => ERDisabled
          | inr1 (inr1 (inl1 (Throw (Error msg)))) => ERError msg
          | inr1 (inr1 (inr1 o')) =>
            match o' in debugE Y return X = Y -> _ with
            | Debug msg => fun pf =>
                            dcall msg (fun 'tt =>
                                         exec_helper bound (k (eq_rect_r (fun T => T) tt pf)))
            end eq_refl
          end
        end
      end.

    Definition exec (bound : nat) (mem : list (thread_id_t * instruction_id_t * mem_write))
               (entry_locs : list mem_loc)
      : exec_result :=
      let it := run mem entry_locs in
      exec_helper bound it.
  End Execute.
End Make.
