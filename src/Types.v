From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Lists.ListSet
     (* Strings.String *)
     Morphisms
     Setoid
     RelationClasses .

(* From ExtLib Require Import *)
(*      Data.String *)
(*      Structures.Monad *)
(*      Structures.Traversable *)
(*      Data.List. *)

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Import ListNotations.

Local Open Scope list.
Local Open Scope itree_scope.
(* Local Open Scope monad_scope. *)

Inductive tree (T : Type) : Type :=
| Tree : T -> list (tree T) -> tree T.
Arguments Tree {T}.

Fixpoint tree_map_with_context {T Y : Type}
         (f : list T -> T -> list (tree T) -> Y) (pref : list T) (t : tree T)
  : tree Y :=
  let '(Tree x ts) := t in
  Tree (f pref x ts) (List.map (tree_map_with_context f (x::pref)) ts).

Definition id_t := nat.

Variant wrapE {T}: Type -> Type :=
| Wrap : forall A E, T -> E A -> wrapE A.

Module Type InstructionsSemantics.
  Variable reg : Type.
  Variable reg_size : reg -> nat.

  (* `(a,b)` represents all the bits between `a` and `b`, including `a` but not
  including `b`. *)
  Definition reg_slc : Type := reg * (nat * nat).
  Definition reg_val : Type := N.

  Variable mem_read_kind : Type.
  Variable mem_write_kind : Type.

  Variable ast : Type.

  Variable regs_from_ast
    : ast -> (ListSet.set reg_slc * ListSet.set reg_slc * ListSet.set reg_slc).

  Context {E : Type -> Type}.

  Variant ITEReg : Type -> Type :=
  | ITERegRead : reg_slc -> ITEReg reg_val
  | ITERegWrite : reg_slc -> reg_val -> ITEReg unit.
  Context {HasITEReg : ITEReg -< E}.

  Variant ITEMem : Type -> Type :=
  | ITEMemRead : nat -> ITEMem nat
  | ITEMemWrite : nat -> nat -> ITEMem unit.
  Context {HasITEMem : ITEMem -< E}.

  Definition sem_t := itree E unit.
  Variable denote : ktree E ast unit.
End InstructionsSemantics.

Module Type Arch.
  Declare Module InsSem : InstructionsSemantics.

  Variable instruction_kind : Type.
  Variable instruction_kind_from_ast : InsSem.ast -> instruction_kind.
  (* Variable instruction_semantics_state : Type. *)
End Arch.
