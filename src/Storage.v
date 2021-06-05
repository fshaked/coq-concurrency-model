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

From RecordUpdate Require Import RecordSet.

Import ListMonad.
Import Monads.
Import MonadNotation.
Import ListNotations.

Require Import Utils.
Require Import Types.
Require Import Thread.

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.
(* Local Open Scope monad_scope. *)

Module State (Arc : ArcSig).
  Record state := mk_state { mem : Arc.mem_loc -> option Arc.mem_slc_val }.
  Instance eta_state : Settable _ := settable! mk_state <mem>.

  Definition initial_state (mem : Arc.mem_loc -> option Arc.mem_slc_val) : state :=
    {| mem := mem |}.
End State.
