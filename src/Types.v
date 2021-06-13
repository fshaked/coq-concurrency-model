From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Lists.ListSet
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

(* From ExtLib Require Import *)
(*      Data.String *)
(*      Structures.Monad *)
(*      Structures.Traversable *)
(*      Data.List. *)

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
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

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Utils.
Require Import Decision.

(* [throw Disabled] indicates a disabled transition, backtrack and try a
   different non-det choice. It is intended that [Disabled] can only happen
   immediately after a non-det choice; and whenever there is a non-det option,
   at least one of the choices is not [Disabled]. Hence non-det options can
   easily be pruned to not include [Disabled] deadlocks. *)
Variant disabled : Type := Disabled : disabled.

Definition guard {E} `{exceptE disabled -< E}
           (p : bool) : itree E unit :=
  if p then Ret tt
  else throw Disabled.

(* Indicates a bug in the model *)
Variant error : Type := Error : string -> error.

Definition try_unwrap_option {E} `{exceptE error -< E}
           {T} (x : option T) (msg : string)
  : itree E T :=
  match x with
  | Some x => ret x
  | None => throw (Error msg)
  end.

Variant result A R : Type :=
| Accept : A -> result A R
| Reject : R -> result A R.
Arguments Accept {A R}.
Arguments Reject {A R}.

Definition thread_id_t := Utils.id_t.
Definition instruction_id_t := Utils.id_t.
Definition mem_read_id_t := Utils.id_t.
Definition mem_write_id_t := Utils.id_t.

Definition mem_loc : Type := nat.
Record mem_slc : Type :=
  mk_mem_slc { location : mem_loc;
               size : nat (* in bytes *) }.
(* [mem_slc_val] is a list of byte values, head is least significant. *)
Definition mem_slc_val : Type := list nat.

Definition flatten_mem_slc_vals (slc : mem_slc) (vals : list (mem_slc * mem_slc_val))
  : option mem_slc_val :=
  let byte_locs := List.seq slc.(location) slc.(size) in
  let byte_of_val slc val (loc : nat) :=
      if decide (slc.(location) <= loc < (slc.(location) + slc.(size))) then
        List.nth_error val (loc - slc.(location))
      else None in
  let fix byte_of_vals vals loc :=
      match vals with
      | (slc', val')::vals' =>
        match byte_of_val slc' val' loc with
        | Some b => Some b
        | None => byte_of_vals vals' loc
        end
      | [] => None
      end in
  let bytes := List.map (byte_of_vals vals) byte_locs in
  List.fold_left (fun acc b =>
                    match acc, b with
                    | Some acc, Some b => Some (b::acc)
                    | _, _ => None
                    end)
                 bytes
                 (Some nil).

Definition nat_of_mem_slc_val (val : mem_slc_val) : nat :=
  List.fold_left
    (fun acc b => (Nat.shiftl acc 8) + b)
    (List.rev val) 0.

Definition mem_slc_val_of_nat (val : nat) (size : nat) : mem_slc_val :=
  List.map
    (fun off => Nat.land (2 ^ 8 - 1) (Nat.shiftr val (8 * off)))
    (List.seq 0 size).

Module Type InstructionSemanticsSig.
  Variable reg : Type.
  Variable reg_eqb : reg -> reg -> bool.
  Variable reg_size : reg -> nat.

  (* `(a,b)` represents all the bits between `a` and `b`, including `a` but not
  including `b`. *)
  Definition reg_slc : Type := reg * (nat * nat).
  Definition reg_slc_eqb (s1 s2 : reg_slc) : bool :=
    let '(r1, (a1, b1)) := s1 in
    let '(r2, (a2, b2)) := s2 in
    reg_eqb r1 r2 && Nat.eqb a1 a2 && Nat.eqb b1 b2.

  Definition reg_val : Type := N.

  Variable mem_read_kind : Type.
  Variable mem_write_kind : Type.

  Variable ast : Type.

  Variable regs_from_ast
    : ast -> (list (reg_slc * bool) * list reg_slc).

  Variant regE : Type -> Type :=
  | RegERead : reg_slc -> regE reg_val
  | RegEWrite : reg_slc -> reg_val -> regE unit.

  Variant memE : Type -> Type :=
  | MemERead : mem_slc -> memE mem_slc_val
  | MemEWriteFP : mem_slc -> memE unit
  | MemEWriteVal : mem_slc_val -> memE unit.

  Definition E := (regE +' memE).

  Variable denote : ktree E ast unit.

  Definition machine_code : Type := nat.
  Variable decode : machine_code -> ast.

  Definition pc_t : Type := nat.
  Variable next_pc : pc_t -> ast -> list pc_t.
End InstructionSemanticsSig.

Module Type ArcSig.
  Declare Module InsSem : InstructionSemanticsSig.

  Variable instruction_kind : Type.
  Variable instruction_kind_from_ast : InsSem.ast -> instruction_kind.

  Variable split_load_mem_slc : instruction_kind -> mem_slc -> list mem_slc.
  Variable split_store_mem_slc_val : instruction_kind -> mem_slc -> mem_slc_val ->
                                     list (mem_slc * mem_slc_val).

  Variable mem_read_kind_of_ins_kind : instruction_kind -> InsSem.mem_read_kind.
  Variable mem_write_kind_of_ins_kind : instruction_kind -> InsSem.mem_read_kind.
End ArcSig.

Module Type ThreadSig.
End ThreadSig.
