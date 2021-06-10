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

  Definition thread_it {E}
             `{wrapE ThrDenote.threadE (Thread.instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             '((loc, tid) : nat * thread_id_t)
    : itree E (Types.result unit unit) :=
    (* TODO: convert loc from nat to Arc.InsSem.pc_t *)
    let it := ThrDenote.denote (0, loc) in
    let it := map_wrap_event_in_it ThrDenote.threadE (fun iid => (iid, tid)) _ it in
    resum_it _ it.

  Definition denote {E}
             `{wrapE ThrDenote.threadE (Thread.instruction_id_t * thread_id_t) -< E}
             `{nondetFinE -< E}
             (entry_locs : list nat)
    : itree E unit :=
    let it :=
        List.length entry_locs
        $> List.seq 0
        $> List.combine entry_locs
        $> List.map thread_it
        $> scheduler
             (fun 'tt => ITree.spin) (* spawn *)
                    (* The spin is unreachable.
                       TODO: do we want to support spawning of new threads?
                       Probably not. *)
             (fun 'tt _ => tt) (* fold_results *)
             tt in (* acc_result *)
    resum_it _ it.

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


  (* Definition handle_thr_memE {E} *)
  (*   : wrapE (wrapE Arc.InsSem.memE Thread.instruction_id_t) thread_id_t ~> stateT state (itree E) := *)
  (*   fun _ e s => *)
  (*     let '(Wrap e tid) := e in *)
  (*     match List.nth_error s.(threads) tid with *)
  (*     | Some thr_state => *)
  (*       '(thr_state, a) <- ThrState.handle_memE _ e thr_state *)
  (*       ;; let ts := list_replace_nth tid thr_state s.(threads) in *)
  (*          Ret (s <| threads := ts |>, a) *)
  (*     | None => ITree.spin (* Unreachable *) *)
  (*     end. *)

  Definition handle_threadE {E}
             `{exceptE disabled -< E}
             `{exceptE system_deadlock -< E}
    : wrapE ThrDenote.threadE (Thread.instruction_id_t * thread_id_t) ~>
            stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e (iid, tid)) := e in
      match List.nth_error s.(threads) tid with
      | Some thr_state =>
        match e with
        | ThEInsFetch loc =>
          match StoState.read_instruction loc s.(storage) with
          | Some (size, code) =>
            (* TODO: pass `size` to the thread so it knows how to increment the PC. *)
            '(thr_state, answer) <- ThrState.handle_ThEInsFetch size code iid thr_state
            ;; let ts := list_replace_nth tid thr_state s.(threads) in
               Ret (s <| threads := ts |>, answer)

            Ret (s, code)
          | None => throw InsNotInStorage
          end

        | ThEInsReadFromSto rid =>
          match ThrState.handle_ThEInsReadFromSto rid iid thr_state with
          | Some (thr_state, read_request) =>
            match StoState.read_data read_request s.(storage) with
            | Some (size, val) =>
              let ts := list_replace_nth tid (thr_state val) s.(threads) in
              Ret (s <| threads := ts |>, true)
            | None => throw ReadFromUnmappedMem
            end
          | None => throw Disabled
          end

        | _ =>
          '(thr_state, answer) <- ThrState.handle_threadE e iid thr_state
          ;; let ts := list_replace_nth tid thr_state s.(threads) in
             Ret (s <| threads := ts |>, answer)
        end
      | None => ITree.spin (* Unreachable *)
      end.

  Definition interp_system {E}
    : itree (wrapE ThrDenote.threadE (Thread.instruction_id_t * thread_id_t) +' E) ~>
            stateT state (itree E) :=
    interp_state (case_ handle_threadE pure_state).

  Definition run_system (mem : nat -> option nat) (entry_locs : list nat) :=
    interp_system (denote entry_locs) (initial_state mem entry_locs).
