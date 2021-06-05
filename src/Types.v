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

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

Variant result : Type :=
| Accept
| Reject.

Module Type InstructionSemanticsSig.
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

  Variant regE : Type -> Type :=
  | RegERead : reg_slc -> regE reg_val
  | RegEWrite : reg_slc -> reg_val -> regE unit.

  Variant memE : Type -> Type :=
  | MemERead : nat -> memE nat
  | MemEWrite : nat -> nat -> memE unit.

  Definition E := (regE +' memE).

  Variable denote : ktree E ast unit.

  Definition machine_code : Type := nat.
  Variable decode : machine_code -> ast.

  Definition pc_t : Type := nat.
  Variable next_pc : pc_t -> ast -> list pc_t.
End InstructionSemanticsSig.

Module Type ArcSig.
  Declare Module InsSem : InstructionSemanticsSig.

  Definition mem_loc := nat.
  Record mem_slc : Type :=
    mk_mem_slc { addr : mem_loc;
                 size: nat (* in bytes *) }.
  Definition mem_slc_val := nat.

  Variable instruction_kind : Type.
  Variable instruction_kind_from_ast : InsSem.ast -> instruction_kind.
  (* Variable instruction_semantics_state : Type. *)
End ArcSig.

Module Type ThreadSig.
End ThreadSig.
