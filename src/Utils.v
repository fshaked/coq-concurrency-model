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

Notation " x '|>' f " := (f x)
  (at level 40, left associativity, only parsing).

Definition resum_it {E F} `{E -< F} : itree E ~> itree F :=
  fun _ it => interp (fun _ e => trigger e) it.

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

Variant nondet_schedulerE (S : Type) : Type -> Type :=
| NondetFin : nat -> nondet_schedulerE S nat
| Spawn : S -> nondet_schedulerE S unit.
Arguments NondetFin {S}.
Arguments Spawn {S}.

CoFixpoint nondet_scheduler {E S}
           (spawn : ktree (nondet_schedulerE S +' E) S unit)
           (its : list (itree (nondet_schedulerE S +' E) unit))
  : itree (nondet_schedulerE S +' E) unit :=
  match its with
  | [] => Ret tt
  | _ =>
    n <- trigger (NondetFin (List.length its))
    ;; match List.nth_error its n with
       | Some it =>
         match observe it with
         | RetF _ => Tau (nondet_scheduler spawn (list_remove_nth n its))
         | TauF it => Tau (nondet_scheduler spawn (list_replace_nth n it its))
         | @VisF _ _ _ X o k =>
           match o with
           | inl1 o' =>
             match o' in nondet_schedulerE _ Y
                   return X = Y -> itree (nondet_schedulerE S +' E) unit with
             | Spawn s =>
               fun pf =>
                 let it := k (eq_rect_r (fun T => T) tt pf) in
                 Tau (nondet_scheduler spawn (spawn s::list_replace_nth n it its))
             | _ => fun _ =>
                     Vis o (fun x => nondet_scheduler spawn (list_replace_nth n (k x) its))
             end eq_refl
           | inr1 _ =>
             Vis o (fun x => nondet_scheduler spawn (list_replace_nth n (k x) its))
           end
         end
       | None => ITree.spin (* catch fire *)
       end
  end.
