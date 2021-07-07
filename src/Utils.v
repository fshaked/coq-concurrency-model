From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     ZArith.ZArith
     Numbers.DecimalString
     Lists.List
     Lists.ListSet
     Strings.String
     Strings.HexString
     Strings.BinaryString
     Morphisms
     Setoid
     RelationClasses
     Vectors.Fin.

Import StringSyntax.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.ListMonad.

From bbv Require Import Word.
Import Word.Notations.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts
     Events.Nondeterminism.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Import ListNotations.

Local Open Scope list.
Local Open Scope itree_scope.
(* Local Open Scope string. *)
(* Local Open Scope monad_scope. *)

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

Require Import Decision.

Definition newline : string := "
".

Section Showable.
  Class Showable A := { show : A -> string }.

  Local Open Scope string_scope.


  #[global] Instance showable_uint : Showable Decimal.uint :=
    { show := NilEmpty.string_of_uint }.

  #[global] Instance showable_nat : Showable nat :=
    { show := fun n => show (Nat.to_uint n) }.

  Variant hex_nat := Hex : nat -> hex_nat.

  #[global] Instance showable_hex_nat : Showable hex_nat :=
    { show := fun '(Hex n) => HexString.of_nat n }.

  #[global] Instance showable_int : Showable Decimal.int :=
    { show := NilEmpty.string_of_int }.

  #[global] Instance showable_Z : Showable Z :=
    { show := fun z => NilEmpty.string_of_int (Z.to_int z)%Z }.

  #[global] Instance showable_word : forall sz, Showable (word sz) :=
    { show := fun w => HexString.of_N (wordToN w) }.

  #[global] Instance showable_list : forall T, Showable T -> Showable (list T) :=
    { show := fun ts =>
                "[" ++ String.concat "; " (List.map show ts) ++ "]"
    }.
End Showable.

Variant debugE : Type -> Type :=
| Debug : string -> debugE unit.

Section List.
  Fixpoint list_replace_nth {T} (n : nat) (x : T) (l : list T) : list T :=
    match n, l with
    | O, _::t => x::t
    | S n, h::t => h::list_replace_nth n x t
    | _, _ => nil
    end.

  Fixpoint list_remove_nth {T} (n : nat) (l : list T) : list T :=
    match n, l with
    | O, _::t => t
    | S n, h::t => h::list_remove_nth n t
    | _, _ => nil
    end.

  Fixpoint list_nth {A} (l : list A) (f : Fin.t (List.length l)) : A :=
  match l return Fin.t (List.length l) -> A with
  | [] => Fin.case0 _ (* unreachable *)
  | h::tl => fun f =>
    match f in Fin.t (S n) return List.length tl = n -> A with
    | F1 => fun _ => h
    | FS fs => fun pf => list_nth tl (eq_rect_r Fin.t fs pf)
    end eq_refl
  end f.

  Fixpoint list_find_index {A} (l : list A) (p : A -> bool) : option (Fin.t (List.length l)) :=
    match l with
    | [] => None
    | h::tl =>
      if p h then Some F1
      else match list_find_index tl p with
           | Some f => Some (FS f)
           | None => None
           end
    end.

  Example list_find_index_0 :
    option_map (fun f => proj1_sig (Fin.to_nat f))
               (list_find_index [1; 2; 3] (fun n => n =? 1)) = Some 0%nat.
  Proof. intros. reflexivity. Qed.

  Example list_find_index_1 :
    option_map (fun f => proj1_sig (Fin.to_nat f))
               (list_find_index [1; 2; 3] (fun n => n =? 2)) = Some 1%nat.
  Proof. intros. reflexivity. Qed.

  Example list_find_index_miss :
    option_map (fun f => proj1_sig (Fin.to_nat f))
               (list_find_index [1; 2; 3] (fun n => n =? 0)) = None.
  Proof. intros. reflexivity. Qed.

  Lemma list_find_index_empty : forall A p, @list_find_index A [] p = None.
  Proof. intros. reflexivity. Qed.
End List.

Section Tree.
  Inductive tree (N L : Type) : Type :=
  | TLeaf : L -> tree N L
  | TNode : N -> list (tree N L) -> tree N L.
  #[global] Arguments TLeaf {N L}.
  #[global] Arguments TNode {N L}.

  Fixpoint tree_map_in_context {N L N' L' : Type}
           (fn : list N' -> N -> list (tree N L) -> N')
           (fl : list N' -> L -> L')
           (pref : list N') (t : tree N L)
    : tree N' L' :=
    match t with
    | TNode n ts =>
      let n := fn pref n ts in
      TNode n (List.map (tree_map_in_context fn fl (n::pref)) ts)
    | TLeaf l => TLeaf (fl pref l)
    end.

  Definition tree_map {N L N' L' : Type} (fn : N -> N') (fl : L -> L')
    : tree N L -> tree N' L' :=
    tree_map_in_context (fun _ n _ => fn n) (fun _ l => fl l) [].

  Fixpoint tree_to_list_preorder {N L : Type} (t : tree N L) : list (N + L) :=
    match t with
    | TNode n ts =>
      (inl n) :: List.concat (List.map tree_to_list_preorder ts)
    | TLeaf l => [inr l]
    end.
End Tree.

Definition id_t := nat.

Definition resum_it {E F} `{E -< F} : itree E ~> itree F :=
  fun _ it => translate subevent it.
(* Alternatively: fun _ it => interp (fun _ e => trigger e) it. *)



Section WrapEvent.
  Variant wrapE E T : Type -> Type :=
  | Wrap : forall A, E A -> T -> wrapE E T A.
  #[global] Arguments Wrap {E T A}.

  Definition wrap_event_in_it (E : Type -> Type) {T : Type} (t : T) {F}
    : itree (E +' F) ~> itree (wrapE E T +' F) :=
    fun _ it =>
      let handle_E : E ~> itree (wrapE E T) := fun _ e => trigger (Wrap e t) in
      let h := bimap handle_E (id_ F) in
      interp h it.

  Definition map_wrap_event_in_it (E : Type -> Type) {T U : Type} (f : T -> U) {F}
    : itree (wrapE E T +' F) ~> itree (wrapE E U +' F) :=
    fun _ it =>
      let handle_WE : wrapE E T ~> itree (wrapE E U) := fun _ '(Wrap e t) => trigger (Wrap e (f t)) in
      let h := bimap handle_WE (id_ F) in
      interp h it.
End WrapEvent.


Section Nondet.
  Variant nondetFinE : Type -> Type :=
  | NondetFin (n : nat) : nondetFinE (Fin.t n).

  Definition choose {E} `{nondetFinE -< E}
             {X} : ktree E (list X) X :=
    fun l =>
      n <- trigger (NondetFin (List.length l))
      ;; ret (list_nth l n).
End Nondet.


Section Scheduler.
  (* [StartExc] starts exclusive execution of the issuing itree, untill it issues
   [EndExc]. *)
  Variant schedulerE (S : Type) : Type -> Type :=
  | Spawn : S -> schedulerE S unit
  | Kill : list S -> schedulerE S unit
  | StartExc : schedulerE S unit
  | EndExc : schedulerE S unit.
  #[global] Arguments Spawn {S}.
  #[global] Arguments Kill {S}.
  #[global] Arguments StartExc {S}.
  #[global] Arguments EndExc {S}.

  Definition exclusive_block {E R S F}
             `{schedulerE S -< F} `{E -< F}
             (b : itree E R)
    : itree F R :=
    'tt <- trigger StartExc
    ;; r <- resum_it _ b
    ;; 'tt <- trigger EndExc
    ;; ret r.

  Definition is_eager {E S IR}
             (is_eager_event : forall A, (schedulerE S +' E) A -> bool)
             (it : itree (schedulerE S +' E) IR)
    : bool :=
    match observe it with
    | RetF _ => true
    | TauF _ => true
    | @VisF _ _ _ X o k => is_eager_event X o
    end.

  Definition scheduler_helper {E S IR R}
             (scheduler : R ->
                          (list (S * itree (schedulerE S +' E) IR)) ->
                          (option S) ->
                          itree (nondetFinE +' E) R)
             (eqb_S : S -> S -> bool)
             (spawn : ktree (schedulerE S +' E) S IR)
             (is_eager_event : forall A, (schedulerE S +' E) A -> bool)
             (fold_results : R -> IR -> R)
             (acc_result : R)
             (its : list (S * itree (schedulerE S +' E) IR))
             (exclusive : option S)
    : itree (nondetFinE +' E) R :=
    match its with
    | [] => Ret acc_result
    | _ =>
      n <- match exclusive with
          | Some id =>
            match list_find_index its (fun '(id', _) => eqb_S id' id) with
            | Some n => Ret n
            | None =>
              (* The exclusive itree killed itslef before ending the exclusive
                 block. Maybe make this an error? *)
              trigger (NondetFin (List.length its))
            end
          | None =>
            match List.find (fun '(_, it) => is_eager is_eager_event it) its with
            | Some (id, _) =>
              match list_find_index its (fun '(id', _) => eqb_S id' id) with
              | Some n => Ret n
              | None => (* unreachable *)
                trigger (NondetFin (List.length its))
              end
            | None => trigger (NondetFin (List.length its))
            end
          end
      ;; let '(id, it) := list_nth its n in
         match observe it with
         | RetF r =>
           let its := list_remove_nth (proj1_sig (Fin.to_nat n)) its in
           Tau (scheduler (fold_results acc_result r) its exclusive)
         | TauF it =>
           let its := list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its in
           Tau (scheduler acc_result its exclusive)
         | @VisF _ _ _ X o k =>
           match o with
           | inl1 o' =>
             match o' in schedulerE _ Y
                   return X = Y -> itree (nondetFinE +' E) R with
             | Spawn id' =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := (id', spawn id')::list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its in
                 Tau (scheduler acc_result its exclusive)
             | Kill ids' =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its in
                 let its := List.filter
                              (* Remove all the itrees with id in [ids'] *)
                              (fun '(id', _) => negb (List.existsb (eqb_S id') ids'))
                              its in
                 Tau (scheduler acc_result its exclusive)
             | StartExc =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its in
                 Tau (scheduler acc_result its (Some id))
             | EndExc =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its in
                 Tau (scheduler acc_result its None)
             end eq_refl
           | inr1 o' =>
             Vis (inr1 o') (fun x =>
                              let its := list_replace_nth (proj1_sig (Fin.to_nat n)) (id, k x) its in
                              scheduler acc_result its exclusive)
           end
         end
    end.

  CoFixpoint scheduler {E S IR R}
             (eqb_S : S -> S -> bool)
             (spawn : ktree (schedulerE S +' E) S IR)
             (is_eager_event : forall A, (schedulerE S +' E) A -> bool)
             (fold_results : R -> IR -> R)
             (acc_result : R)
             (its : list (S * itree (schedulerE S +' E) IR))
             (exclusive : option S)
    : itree (nondetFinE +' E) R :=
    scheduler_helper (scheduler eqb_S spawn is_eager_event fold_results)
                     eqb_S spawn is_eager_event fold_results acc_result its exclusive.
End Scheduler.


Section Slices.
  Class Slice (T : Type) := { start : T -> nat;
                              size : T -> nat;
                              sub_slice : T -> nat -> nat -> option T }.

  Definition reads_from_slcs_helper_helper {S S'} `{Slice S} `{Slice S'}
             (slc : S) (uslc : S')
    : option (option (S * list S')) :=
    if decide (start slc < start uslc + size uslc /\
               start uslc < start slc + size slc)%nat then
      let slc'_start := max (start slc) (start uslc) in
      let slc'_end := min ((start slc) + (size slc)) ((start uslc) + (size uslc)) in
      match sub_slice slc slc'_start (slc'_end - slc'_start) with
      | Some slc' =>

        match
            (if decide (start uslc < start slc')%nat then
               match sub_slice uslc (start uslc) ((start slc') - (start uslc)) with
               | Some s => Some [s]
               | None => None
               end
            else Some nil),
            (if decide (slc'_end < (start uslc) + (size uslc))%nat then
               match sub_slice uslc slc'_end ((start uslc) + (size uslc) - slc'_end) with
               | Some s => Some [s]
               | None => None
               end
            else Some nil)
        with
        | Some uslcs1, Some uslcs2 => Some (Some (slc', uslcs1 ++ uslcs2))
        | _, _ => None
        end
      | None => None
      end
    else
      Some None.

  Fixpoint reads_from_slcs_helper {S S'} `{Slice S} `{Slice S'}
           (slc : S)
           (uslcs : list S')
           (acc_rf : list S)
           (acc_uslcs : list S')
    : option (list S * list S') :=
    match uslcs with
    | uslc::uslcs =>
      match reads_from_slcs_helper_helper slc uslc with
      | Some (Some (slc', uslcs')) =>
        reads_from_slcs_helper slc uslcs (slc'::acc_rf) (uslcs' ++ acc_uslcs)
      | Some None =>
        reads_from_slcs_helper slc uslcs acc_rf (uslc::acc_uslcs)
      | None => None
      end
    | nil => Some (acc_rf, acc_uslcs)
    end.

  Fixpoint reads_from_slcs {S S'} `{Slice S} `{Slice S'}
           (slcs : list S)
           (uslcs : list S')
           (rf : list S)
    : option (list S * list S') :=
    match slcs with
    | slc::slcs =>
      match reads_from_slcs_helper slc uslcs rf [] with
      | Some (rf', uslcs') => reads_from_slcs slcs uslcs' rf'
      | None => None
      end
    | nil => Some (rf, uslcs)
    end.
End Slices.
