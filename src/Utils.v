From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Lists.ListSet
     Morphisms
     NArith.NArith
     Numbers.DecimalString
     RelationClasses
     Setoid
     Strings.BinaryString
     Strings.HexString
     Strings.String
     Vectors.Fin
     ZArith.ZArith.

Import StringSyntax.

From ExtLib Require Import
     Core.RelDec
     Data.Map.FMapAList
     Data.Monads.ListMonad
     Structures.Maps
     Structures.Monads.

From bbv Require Import Word.
Import Word.Notations.

From ITree Require Import
     Events.MapDefault
     Events.Nondeterminism
     Events.StateFacts
     ITree
     ITreeFacts.

Import ITreeNotations.
Import ListNotations.
Import MonadNotation.
Import Monads.

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
  Variant chooseE (T : Type) : Type -> Type :=
  | Choose : list T -> chooseE T T.
  #[global] Arguments Choose {T}.

  Definition nondet {E T} `{chooseE nat -< E}
    : ktree E (list T) (option T) :=
    fun l =>
      n <- trigger (Choose (List.seq 0 (List.length l)))
      ;; ret (List.nth_error l n).
End Nondet.


Section Scheduler.
  (* [StartExc] starts exclusive execution of the issuing itree, untill it issues
   [EndExc]. *)
  Variant schedulerE (S : Type) : Type -> Type :=
  | Spawn : S -> schedulerE S unit
  | Kill : S -> schedulerE S unit
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

  CoFixpoint scheduler {E S I R R'}
             `{RelDec S (@eq S)}
             (spawn : ktree (schedulerE S +' E) S R)
             (hash_next : itree (schedulerE S +' E) R -> I)
             (fold_results : R' -> R -> R')
             (acc_result : R')
             (its : alist S (itree (schedulerE S +' E) R))
             (exclusive : option S)
    : itree (chooseE (S * I) +' E) R' :=
    match its with
    | [] => Ret acc_result
    | (id, it)::_ =>
      id <- match exclusive with
           | Some id => Ret id
           | None =>
             let es := List.map (fun '(id, it) => (id, hash_next it)) its in
             '(id, _) <- trigger (Choose es)
             ;; ret id
           end
      ;; let it := match lookup id its with
                   | Some it => it
                   | None => it (* FIXME: error? *)
                   end in
         match observe it with
         | RetF r =>
           let its := Maps.remove id its in
           Tau (scheduler spawn hash_next fold_results (fold_results acc_result r) its None)
         | TauF it =>
           let its := Maps.add id it its in
           Tau (scheduler spawn hash_next fold_results acc_result its exclusive)
         | @VisF _ _ _ X o k =>
           match o with
           | inl1 o' =>
             match o' in schedulerE _ Y
                   return X = Y -> itree (chooseE (S * I) +' E) R' with
             | Spawn id' =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := Maps.add id' (spawn id') (Maps.add id it its) in
                 Tau (scheduler spawn hash_next fold_results acc_result its exclusive)
             | Kill id' =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := Maps.add id it its in
                 let its := Maps.remove id' its in
                 let exclusive := if rel_dec id id' then
                                    (* A thread just killed itslef *)
                                    None
                                  else exclusive in
                 Tau (scheduler spawn hash_next fold_results acc_result its exclusive)
             | StartExc =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := Maps.add id it its in
                 Tau (scheduler spawn hash_next fold_results acc_result its (Some id))
             | EndExc =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 let its := Maps.add id it its in
                 Tau (scheduler spawn hash_next fold_results acc_result its None)
             end eq_refl
           | inr1 o' =>
             Vis (inr1 o') (fun x => let its := Maps.add id (k x) its in
                                  scheduler spawn hash_next fold_results acc_result its exclusive)
           end
         end
    end.
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
