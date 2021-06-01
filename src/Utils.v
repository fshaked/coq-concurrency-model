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



Variant nondet_finE : Type -> Type :=
| NondetFin : nat -> nondet_finE nat.

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
