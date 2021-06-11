From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Lists.ListSet
     (* Strings.String *)
     Morphisms
     Setoid
     RelationClasses
     Vectors.Fin.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.ListMonad.

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
(* Local Open Scope monad_scope. *)

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

Notation " x '$>' f " := (f x)
  (at level 40, left associativity, only parsing).


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


Inductive tree (T : Type) : Type :=
| Tree : T -> list (tree T) -> tree T.
Arguments Tree {T}.

Fixpoint tree_map_with_context {T Y : Type}
         (f : list T -> T -> list (tree T) -> Y) (pref : list T) (t : tree T)
  : tree Y :=
  let '(Tree x ts) := t in
  Tree (f pref x ts) (List.map (tree_map_with_context f (x::pref)) ts).

Definition id_t := nat.



Definition resum_it {E F} `{E -< F} : itree E ~> itree F :=
  fun _ it => interp (fun _ e => trigger e) it.

Variant wrapE E T : Type -> Type :=
| Wrap : forall A, E A -> T -> wrapE E T A.
Arguments Wrap {E T A}.

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

Variant nondetFinE : Type -> Type :=
| NondetFin (n : nat) : nondetFinE (Fin.t n).

Fixpoint list_nth {A} (l : list A) (f : Fin.t (List.length l)) : A :=
  match l return Fin.t (length l) -> A with
  | [] => Fin.case0 _ (* unreachable *)
  | h::tl => fun f =>
    match f in Fin.t (S n) return length tl = n -> A with
    | F1 => fun _ => h
    | FS fs => fun pf => list_nth tl (eq_rect_r Fin.t fs pf)
    end eq_refl
  end f.

Definition choose {E} `{nondetFinE -< E}
           {X} : ktree E (list X) X :=
  fun l =>
    n <- trigger (NondetFin (List.length l))
    ;; ret (list_nth l n).

Variant schedulerE (S : Type) : Type -> Type :=
| Spawn : S -> schedulerE S unit
| Kill : S -> schedulerE S unit.
Arguments Spawn {S}.
Arguments Kill {S}.

CoFixpoint scheduler {E S IR R}
           (eq_dec_S : forall (x y : S), {x = y}+{x <> y})
           (spawn : ktree (schedulerE S +' E) S IR)
           (fold_results : R -> IR -> R)
           (acc_result : R)
           (its : list (S * itree (schedulerE S +' E) IR))
  : itree (nondetFinE +' E) R :=
  match its with
  | [] => Ret acc_result
  | _ =>
    n <- trigger (NondetFin (List.length its))
    ;; let '(id, it) := list_nth its n in
       match observe it with
       | RetF r =>
         let acc_result := fold_results acc_result r in
         Tau (scheduler eq_dec_S spawn fold_results acc_result
                        (list_remove_nth (proj1_sig (Fin.to_nat n)) its))
       | TauF it =>
         Tau (scheduler eq_dec_S spawn fold_results acc_result
                        (list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its))
       | @VisF _ _ _ X o k =>
         match o with
         | inl1 o' =>
           match o' in schedulerE _ Y
                 return X = Y -> itree (nondetFinE +' E) R with
           | Spawn id' =>
             fun pf =>
               let it := k (eq_rect_r (fun T => T) tt pf) in
               Tau (scheduler eq_dec_S spawn fold_results acc_result
                              ((id', spawn id')::list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its))
           | Kill id' =>
             fun pf =>
               let it := k (eq_rect_r (fun T => T) tt pf) in
               let its := list_replace_nth (proj1_sig (Fin.to_nat n)) (id, it) its in
               let its := List.filter (fun '(id'', _) => if eq_dec_S id'' id' then false else true) its in
               Tau (scheduler eq_dec_S spawn fold_results acc_result its)
           end eq_refl
         | inr1 o' =>
           Vis (inr1 o') (fun x => scheduler eq_dec_S spawn fold_results acc_result
                                          (list_replace_nth (proj1_sig (Fin.to_nat n)) (id, (k x)) its))
         end
       end
  end.
