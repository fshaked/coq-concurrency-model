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

Definition reads_from_slc (slc : mem_slc) (val : mem_slc_val) (uslc : mem_slc)
  : option (mem_slc * mem_slc_val * list mem_slc) :=
  if decide (slc.(location) < uslc.(location) + uslc.(size) /\
             uslc.(location) < slc.(location) + slc.(size)) then
    let val_start := max slc.(location) uslc.(location) in
    let val_end := min (slc.(location) + slc.(size)) (uslc.(location) + uslc.(size)) in

    let slc' := {| location := val_start;
                   size := val_end - val_start |} in
    let val' := List.firstn slc'.(size) (List.skipn (slc'.(location) - slc.(location)) val) in

    let uslcs' :=
        if decide (uslc.(location) < slc'.(location)) then
          {| location := uslc.(location);
             size := slc'.(location) - uslc.(location) |}::nil
        else nil in
    let uslcs' :=
        if decide (val_end < uslc.(location) + uslc.(size)) then
          {| location := val_end;
             size := uslc.(location) + uslc.(size) - val_end |}::uslcs'
        else uslcs' in

    Some (slc', val', uslcs')
  else
    None.

Fixpoint reads_from {T} (eqb_T : T -> T -> bool)
         (vals : list (T * (mem_slc * mem_slc_val)))
         (uslcs : list mem_slc)
         (rf : list (T * (mem_slc * mem_slc_val)))
  : list mem_slc * list (T * (mem_slc * mem_slc_val)) :=
  match vals with
  | (id, (slc, val))::vals =>
    let '(rf', uslcs') :=
        List.split
          (List.map (fun uslc =>
                       match reads_from_slc slc val uslc with
                       | Some (slc', val', uslcs') =>
                         (Some (id, (slc', val')), uslcs')
                       | None => (None, [uslc])
                       end) uslcs) in
    let rf := List.fold_left (fun rf val =>
                                match val with
                                | Some val => val::rf
                                | None => rf
                                end) rf' rf in
    let uslcs' := List.concat uslcs' in
    reads_from eqb_T vals uslcs rf
  | nil => (uslcs, rf)
  end.

Fixpoint mem_slc_val_of_reads_from_helper {T}
           (slc : mem_slc) (vals : list (T * (mem_slc * mem_slc_val)))
           (val : list (option nat))
  : list (option nat) :=
  match vals with
  | nil => val
  | (_, (s, v))::vals =>
    let val :=
        List.fold_left (fun val '(i, b) => list_replace_nth i (Some b) val)
                       (List.combine (List.seq (s.(location) - slc.(location)) s.(size)) v)
                       val in
    mem_slc_val_of_reads_from_helper slc vals val
  end.

Definition mem_slc_val_of_reads_from {T}
           (slc : mem_slc) (vals : list (T * (mem_slc * mem_slc_val)))
  : option mem_slc_val :=
  let bytes := mem_slc_val_of_reads_from_helper slc vals (List.repeat None slc.(size)) in
  if decide (Forall (fun b => b <> None) bytes) then
    Some (List.map (fun b => match b with Some b => b | None => 0 end) bytes)
  else None.

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

  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id_t;
                  read_footprint : mem_slc;
                  read_kind : InsSem.mem_read_kind }.

  Record mem_write : Type :=
    mk_mem_write { write_id : mem_write_id_t;
                   write_footprint : mem_slc;
                   write_val : mem_slc_val;
                   write_kind : InsSem.mem_read_kind }.

  Definition mem_reads_from : Type := list ((thread_id_t * instruction_id_t * mem_write_id_t) *
                                            (mem_slc * mem_slc_val)).
End ArcSig.

Module Type ThreadSig.
End ThreadSig.
