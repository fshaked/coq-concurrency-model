From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Strings.String.

Import ListNotations.

From bbv Require Import Word.
Import Word.Notations.

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
     Events.State.

Import Monads.
Import ITreeNotations.

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

Instance slice_mem_slc : Slice mem_slc :=
  { start := location;
    size := size;
    sub_slice := fun s start size => Some ({| location := start;
                                           size := size |}) }.

Instance slice_mem_slc_val : Slice (mem_slc * mem_slc_val) :=
  { start := fun '(s, _) => s.(location);
    size := fun '(s, _) => s.(size);
    sub_slice := fun '(s, v) start size =>
                   let s' := {| location := start;
                                size := size |} in
                   let v' := List.firstn size (List.skipn (start - s.(location)) v) in
                   Some (s', v') }.

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

Module Type InsSemCoreSig.
  Variable reg : Type.
  Variable reg_eqb : reg -> reg -> bool.
  Variable reg_size : reg -> nat. (* Size in bits *)

  (* TODO: The Arm ARM pseudocode passes this kind of attributes when doing the
  actuall memory access (e.g., AArch64.MemSingle), but the concurrency model
  needs this information earlier. *)
  Variable mem_read_kind : Type.
  Variable mem_write_kind : Type.

  Variable ast : Type.
End InsSemCoreSig.

Module InsSemCoreFacts (Core : InsSemCoreSig).
  (* `(i,s)` represents all the bits between `i` and `i+s`, including `i` but not
  including `i+s`. *)
  Record reg_slc := { rs_reg : Core.reg;
                      rs_first_bit : nat;
                      rs_size : nat }.

  Instance slice_reg_slc : Slice reg_slc :=
    { start := rs_first_bit;
      size := rs_size;
      sub_slice := fun s start size => Some ({| rs_reg := s.(rs_reg);
                                             rs_first_bit := start;
                                             rs_size := size |}) }.

  Definition reg_slc_eqb (s1 s2 : reg_slc) : bool :=
    Core.reg_eqb s1.(rs_reg) s2.(rs_reg) &&
    Nat.eqb s1.(rs_first_bit) s2.(rs_first_bit) &&
    Nat.eqb s1.(rs_size) s2.(rs_size).

  Definition reg_val := word.
  Definition reg_val_add {sz} (r1 : reg_val sz) (r2 : reg_val sz) : reg_val sz := wplus r1 r2.
  Definition reg_val_of_nat (sz n : nat) : reg_val sz := natToWord sz n.
  Definition nat_of_reg_val {sz : nat} (n : reg_val sz) : nat := wordToNat n.
  Fixpoint reg_val_of_mem_slc_val (sz : nat) (v : mem_slc_val) : reg_val sz :=
    reg_val_of_nat sz (nat_of_mem_slc_val v).
    (* match v with *)
    (* | nil => 0%N *)
    (* | h::tl => ((N.of_nat h) + (N.shiftl (reg_val_of_mem_slc_val tl) 8))%N *)
    (* end. *)
  Fixpoint mem_slc_val_of_reg_val {sz : nat} (n : reg_val sz)
    : mem_slc_val :=
    mem_slc_val_of_nat (nat_of_reg_val n) (sz / 8).
    (* let byte_mask := ((2 ^ 8) - 1)%N in *)
    (* match size with *)
    (* | O => nil *)
    (* | S size => *)
    (*   N.to_nat (N.land byte_mask n) :: mem_slc_val_of_reg_val (N.shiftr n 8) size *)
    (* end. *)
  Definition mem_loc_of_reg_val {sz : nat} (n : reg_val sz) : mem_loc :=  nat_of_reg_val n.
  Definition reg_val_of_mem_loc (sz : nat) (loc : mem_loc) : reg_val sz := reg_val_of_nat sz loc.

  Record reg_slc_val := { rsv_slc : reg_slc;
                          rsv_val : option (reg_val rsv_slc.(rs_size)) }.

  Program Instance slice_reg_slc_val : Slice reg_slc_val :=
    { start := fun s => start s.(rsv_slc);
      size := fun s => Utils.size s.(rsv_slc); }.
  Obligation 1.
  rename X into rsv. rename H into start. rename H0 into size.
  destruct rsv; destruct rsv_val0.
  - destruct (decide (Utils.start rsv_slc0 <= start /\
                      start - (Utils.start rsv_slc0) + size <= (Utils.size rsv_slc0)))
      as [[Hl1 Hl2]|].
    + remember ((start - (Utils.start rsv_slc0)) + size) as lsbs eqn:Hlsbs.
      destruct rsv_slc0; simpl in *.
      assert (Hv1 : lsbs + (rs_size0 - lsbs) = rs_size0).
      { rewrite Nat.add_comm. rewrite Nat.sub_add; auto. }
      assert (Hv2 : lsbs - size + size = lsbs).
      { rewrite Nat.sub_add.
        - reflexivity.
        - rewrite Hlsbs. apply Plus.le_plus_r. }
      rewrite <- Hv1 in r.
      rewrite <- Hv2 in r.
      remember (split1 (lsbs - size + size) (rs_size0 - (lsbs - size + size)) r).
      remember (split2 (lsbs - size) size w).
      apply (Some ({| rsv_slc := {| rs_reg := rs_reg0;
                                    rs_first_bit := start;
                                    rs_size := size |}; rsv_val := Some w0 |})).
    + apply None.
  - apply None.
  Qed.

  Record info :=
    mk_info { input_regs : list (reg_slc * bool);
              output_regs : list reg_slc }.

  Variant regE : Type -> Type :=
  | RegERead (s : reg_slc) : regE (reg_val s.(rs_size))
  | RegEWrite (s : reg_slc) : reg_val s.(rs_size) -> regE unit.

  Variant memE : Type -> Type :=
  | MemERead : mem_slc -> memE mem_slc_val
  | MemEWriteFP : mem_slc -> memE unit
  | MemEWriteVal : mem_slc_val -> memE unit.

  Definition E := (regE +' memE).
End InsSemCoreFacts.

Module Type InsSemSig.
  Declare Module Core : InsSemCoreSig.
  Include Core.
  Include InsSemCoreFacts Core.

  Variable info_of_ast : ast -> info.
  Variable denote : ktree E ast unit.
  Variable decode : mem_slc_val -> option ast.
  (* FIXME: the return type has to also express branches that have no concrete
  value yet. *)
  Variable next_pc : mem_loc -> ast -> list mem_loc.
End InsSemSig.

Module Type ArcCoreSig.
  Declare Module InsSem : InsSemSig.

  (** InsSem-Thread interface *)

  Variable mem_read_kind_of_ast : InsSem.ast -> InsSem.mem_read_kind.
  Variable mem_write_kind_of_ast : InsSem.ast -> InsSem.mem_write_kind.

  Variable split_load_mem_slc : InsSem.ast -> mem_slc -> list mem_slc.
  Variable split_store_mem_slc_val : InsSem.ast -> mem_slc -> mem_slc_val ->
                                     list (mem_slc * mem_slc_val).
End ArcCoreSig.

Module ArcCoreFacts (ArcCore : ArcCoreSig).
  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id_t;
                  read_footprint : mem_slc;
                  read_kind : ArcCore.InsSem.mem_read_kind }.

  Record _mem_write : Type :=
    mk_mem_write { write_id : mem_write_id_t;
                   write_footprint : mem_slc;
                   write_val : mem_slc_val;
                   write_kind : ArcCore.InsSem.mem_write_kind }.
  Definition mem_write := _mem_write.

  Definition mem_reads_from : Type := list ((thread_id_t * instruction_id_t * mem_write_id_t) *
                                            (mem_slc * mem_slc_val)).

  Variant _storageE : Type -> Type :=
  | StEReadInstruction : mem_loc -> _storageE (mem_slc * mem_reads_from)
  | StERead : mem_read -> (list mem_slc) -> _storageE mem_reads_from
  | StEWrite : mem_write -> _storageE unit.
  Definition storageE := _storageE.
End ArcCoreFacts.

Module Type ArcSig.
  Declare Module Core : ArcCoreSig.
  Include Core.
  Include ArcCoreFacts Core.
End ArcSig.


Module Type ThreadSig (Arc : ArcSig).
  Variable state : Type.
  Variable initial_state : instruction_id_t -> mem_loc -> state.

  Variable E : Type -> Type.
  Variable denote : forall (F : Type -> Type)
                      `{HasWrapThreadIID: wrapE E instruction_id_t -< F}
                      `{HasNondetFin: nondetFinE -< F},
      ktree F instruction_id_t (result unit unit).
  Arguments denote {F HasWrapThreadIID HasNondetFin}.

  Variable handle_E : forall (F : Type -> Type)
                        `{HasStorage: Arc.storageE -< F}
                        `{HasState: stateE state -< F}
                        `{HasExceptDisabled: exceptE disabled -< F}
                        `{HasExceptError: exceptE error -< F},
      instruction_id_t -> E ~> itree F.
  Arguments handle_E {F HasStorage HasState HasExceptDisabled HasExceptError}.
End ThreadSig.

Module Type StorageSig (Arc : ArcSig).
  Variable state : Type.
  Variable initial_state : list (thread_id_t * instruction_id_t * Arc.mem_write) -> state.
  Variable handle_storageE : forall (E : Type -> Type)
                               `{HasState: stateE state -< E}
                               `{HasExceptDisabled: exceptE disabled -< E}
                               `{HasExceptError: exceptE error -< E},
                             instruction_id_t -> thread_id_t ->
                             Arc.storageE ~> itree E.
  Arguments handle_storageE {E HasState HasExceptDisabled HasExceptError}.
End StorageSig.
