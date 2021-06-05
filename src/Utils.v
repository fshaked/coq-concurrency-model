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

Definition wrap_it {T E F} `{wrapE E T -< F} (d : T) : itree E ~> itree F :=
  fun _ it => interp (fun _ e => trigger (Wrap e d)) it.


Variant nondet_schedulerE (S : Type) : Type -> Type :=
| NondetFin : nat -> nondet_schedulerE S nat
| Spawn : S -> nondet_schedulerE S unit.
Arguments NondetFin {S}.
Arguments Spawn {S}.

CoFixpoint nondet_scheduler {E S IR R}
           (spawn : ktree (nondet_schedulerE S +' E) S IR)
           (fold_results : R -> IR -> R)
           (acc_result : R)
           (its : list (itree (nondet_schedulerE S +' E) IR))
  : itree (nondet_schedulerE S +' E) R :=
  match its with
  | [] => Ret acc_result
  | _ =>
    n <- trigger (NondetFin (List.length its))
    ;; match List.nth_error its n with
       | Some it =>
         match observe it with
         | RetF r =>
           let acc_result := fold_results acc_result r in
           Tau (nondet_scheduler spawn fold_results acc_result (list_remove_nth n its))
         | TauF it =>
           Tau (nondet_scheduler spawn fold_results acc_result (list_replace_nth n it its))
         | @VisF _ _ _ X o k =>
           match o with
           | inl1 o' =>
             match o' in nondet_schedulerE _ Y
                   return X = Y -> itree (nondet_schedulerE S +' E) R with
             | Spawn s =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 Tau (nondet_scheduler spawn fold_results acc_result(spawn s::list_replace_nth n it its))
             | _ => fun _ =>
                     Vis o (fun x => nondet_scheduler spawn fold_results acc_result (list_replace_nth n (k x) its))
             end eq_refl
           | inr1 _ =>
             Vis o (fun x => nondet_scheduler spawn fold_results acc_result (list_replace_nth n (k x) its))
           end
         end
       | None => ITree.spin (* catch fire *)
       end
  end.
