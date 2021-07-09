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
   easily be pruned to not include [Disabled] deadlocks.
   NOTE: for some reason extract fails without the [unit ->]. *)
Variant disabled : Type := Disabled : unit -> disabled.

Definition guard {E} `{exceptE disabled -< E}
           (p : bool) : itree E unit :=
  if p then Ret tt
  else throw (Disabled tt).

(* Indicates a bug in the model *)
Variant error : Type := Error : string -> error.

Definition guard_some {E} `{exceptE disabled -< E}
           {T} (x : option T)
  : itree E T :=
  match x with
  | Some x => ret x
  | None => throw (Disabled tt)
  end.

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

Variant thread_id := ThreadID : nat -> thread_id.

Instance decision_thread_id_eq : forall (m n : thread_id), Decision (m = n).
Proof. decision_eq. Qed.

Instance showable_thread_id : Showable thread_id :=
  { show := fun '(ThreadID tid) => show tid }.

Variant instruction_id := InstructionID : nat -> instruction_id.

Instance decision_instruction_id_eq : forall (m n : instruction_id), Decision (m = n).
Proof. decision_eq. Qed.

Instance showable_instruction_id : Showable instruction_id :=
  { show := fun '(InstructionID iid) => show iid }.

Variant mem_read_id := MemReadID : nat -> mem_read_id.

Instance decision_mem_read_id_eq : forall (m n : mem_read_id), Decision (m = n).
Proof. decision_eq. Qed.

Instance showable_mem_read_id : Showable mem_read_id :=
  { show := fun '(MemReadID rid) => show rid }.

Variant mem_write_id := MemWriteID : nat -> mem_write_id.

Instance decision_mem_write_id_eq : forall (m n : mem_write_id), Decision (m = n).
Proof. decision_eq. Qed.

Instance showable_mem_write_id : Showable mem_write_id :=
  { show := fun '(MemWriteID wid) => show wid }.

Variant mem_loc : Type := MemLoc : nat -> mem_loc.
Definition mem_loc_to_nat (l : mem_loc) : nat := let '(MemLoc n) := l in n.

Instance showable_mem_loc : Showable mem_loc :=
  { show := fun '(MemLoc n) => show (Hex n) }.

Record mem_slc : Type :=
  mk_mem_slc { location : mem_loc;
               size : nat (* in bytes *) }.

Local Open Scope string_scope.
Instance showable_mem_slc : Showable mem_slc :=
  { show :=
      fun s =>
        let range := match s.(size) with
                     | 0 => "[?]" (* this case should be unreachable *)
                     | 1 => ""
                     | S n => "[" ++ show (Nat.to_uint n) ++ ":0]"
                     end in
        show s.(location) ++ range
  }.
Close Scope string_scope.

(* [mem_slc_val] is a list of byte values, head is least significant. *)
Definition mem_slc_val : Type := list nat.

Instance slice_mem_slc : Slice mem_slc :=
  { start := fun s => mem_loc_to_nat s.(location);
    size := size;
    sub_slice := fun s start size => Some ({| location := (MemLoc start);
                                           size := size |}) }.

Instance slice_mem_slc_val : Slice (mem_slc * mem_slc_val) :=
  { start := fun '(s, _) => mem_loc_to_nat s.(location);
    size := fun '(s, _) => s.(size);
    sub_slice := fun '(s, v) start size =>
                   let s' := {| location := MemLoc start;
                                size := size |} in
                   let v' := List.firstn size (List.skipn (start - (mem_loc_to_nat s.(location))) v) in
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
                       (List.combine (List.seq ((mem_loc_to_nat s.(location)) - (mem_loc_to_nat slc.(location))) s.(size)) v)
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

Definition mem_slc_val_of_nat (val : nat) (size : nat) : mem_slc_val :=
  List.map
    (fun off => Nat.land (2 ^ 8 - 1) (Nat.shiftr val (8 * off)))
    (List.seq 0 size).

Module Type InsSemCoreSig.
  Parameter reg : Type.
  Context `{showable_reg : Showable reg}.
  Context `{decision_reg_eq : forall (m n : reg), Decision (m = n)}.
  Parameter reg_size : reg -> nat. (* Size in bits *)

  (* TODO: The Arm ARM pseudocode passes this kind of attributes when doing the
  actuall memory access (e.g., AArch64.MemSingle), but the concurrency model
  needs this information earlier. *)
  Parameter mem_read_kind : Type.
  Context `{showable_mem_read_kind : Showable mem_read_kind}.
  Parameter mem_write_kind : Type.
  Context `{showable_mem_write_kind : Showable mem_write_kind}.

  Parameter ast : Type.
  Context `{showable_ast : Showable ast}.
End InsSemCoreSig.

Module InsSemCoreFacts (Core : InsSemCoreSig).
  Export Core.
  Existing Instance Core.showable_reg.

  Record reg_slc := { rs_reg : Core.reg;
                      rs_first_bit : nat;
                      rs_size : nat }.

  Local Open Scope string_scope.
  Instance showable_reg_slc : Showable reg_slc :=
    { show :=
        fun s =>
          let range := (* msb:lsb *)
              match s.(rs_size) with
              | 0 => "?" (* this case should not be reachable *)
              | 1 => show (Nat.to_uint s.(rs_first_bit))
              | S n => show (Nat.to_uint (s.(rs_first_bit) + n)) ++ ":" ++ show (Nat.to_uint s.(rs_first_bit))
              end in
          show s.(rs_reg) ++ "<" ++ range ++ ">"
    }.
  Close Scope string_scope.

  #[global] Instance decide_reg_slc_eq : forall (m n : reg_slc), Decision (m = n).
  Proof.
    intros. unfold Decision.
    destruct m, n.
    destruct (Core.decision_reg_eq rs_reg0 rs_reg1), (decide (rs_first_bit0 = rs_first_bit1)), (decide (rs_size0 = rs_size1));
      try (subst; left; reflexivity);
      try (right; unfold not; intros; injection H; intros; auto).
  Qed.

  Instance slice_reg_slc : Slice reg_slc :=
    { start := rs_first_bit;
      size := rs_size;
      sub_slice := fun s start size => Some ({| rs_reg := s.(rs_reg);
                                             rs_first_bit := start;
                                             rs_size := size |}) }.

  Definition reg_val := word.

  Definition reg_val_add {sz} (r1 : reg_val sz) (r2 : reg_val sz) : reg_val sz := wplus r1 r2.
  Definition reg_val_of_nat (sz n : nat) : reg_val sz := natToWord sz n.
  Definition nat_of_reg_val {sz : nat} (n : reg_val sz) : nat := wordToNat n.
  Definition reg_val_of_mem_slc_val (sz : nat) (v : mem_slc_val) : reg_val sz :=
    List.fold_left
      (fun w b => (w ^<< 8) ^| (natToWord sz b))%word
      (List.rev v)
      (Word.wzero sz).
  Definition mem_slc_val_of_reg_val {sz : nat} (n : reg_val sz)
    : mem_slc_val :=
    mem_slc_val_of_nat (nat_of_reg_val n) (sz / 8).
  Definition mem_loc_of_reg_val {sz : nat} (n : reg_val sz) : mem_loc :=  MemLoc (nat_of_reg_val n).
  Definition reg_val_of_mem_loc (sz : nat) (loc : mem_loc) : reg_val sz := reg_val_of_nat sz (mem_loc_to_nat loc).

  Record reg_slc_val := { rsv_slc : reg_slc;
                          rsv_val : option (reg_val rsv_slc.(rs_size)) }.

  Local Open Scope string_scope.
  Instance showable_reg_slc_val : Showable reg_slc_val :=
    { show :=
        fun s => show s.(rsv_slc) ++ " = " ++
                               match s.(rsv_val) with
                               | Some v => show v
                               | None => "?"
                               end
    }.
  Close Scope string_scope.

  Program Instance slice_reg_slc_val : Slice reg_slc_val :=
    { start := fun s => start s.(rsv_slc);
      size := fun s => Utils.size s.(rsv_slc);
      sub_slice := fun rsv start size =>
                     match rsv.(rsv_val) with
                     | Some val =>
                       if decide (Utils.start rsv.(rsv_slc) <= start /\
                                  start - (Utils.start rsv.(rsv_slc)) + size <= (Utils.size rsv.(rsv_slc)))
                       then
                         let lsbs := (start - (Utils.start rsv.(rsv_slc))) + size in
                         let w := split1 (lsbs - size + size) (rsv.(rsv_slc).(rs_size) -
                                                               (lsbs - size + size))
                                         val in
                         let w' := split2 (lsbs - size) size w in
                         Some  ({| rsv_slc := {| rs_reg := rsv.(rsv_slc).(rs_reg);
                                                 rs_first_bit := start;
                                                 rs_size := size |};
                                   rsv_val := Some w' |})
                       else None
                     | None => None
                     end
    }.
  Obligation 1.
  rewrite Nat.add_comm.
  rewrite Nat.sub_add; auto.
  rewrite Nat.sub_add; auto.
  apply Plus.le_plus_r.
  Qed.

  Record info :=
    mk_info { input_regs : list (reg_slc * bool);
              output_regs : list reg_slc }.

  Variant regE : Type -> Type :=
  | RegERead (s : reg_slc) : regE (reg_val s.(rs_size))
  | RegEWrite (s : reg_slc) : reg_val s.(rs_size) -> regE unit.

  Instance showable_regE : forall A, Showable (regE A) :=
    { show :=
        fun e =>
          match e with
          | RegERead s => "RegERead " ++ show s
          | RegEWrite s v => "RegEWrite " ++ show s ++ " " ++ show v
          end%string }.

  Variant memE : Type -> Type :=
  | MemERead : mem_slc -> memE mem_slc_val
  | MemEWriteFP : mem_slc -> memE unit
  | MemEWriteVal : mem_slc_val -> memE unit.

  Definition insSemE := (regE +' memE).
End InsSemCoreFacts.

Module Type InsSemSig.
  Declare Module Core : InsSemCoreSig.
  Module CoreFacts := InsSemCoreFacts Core.
  Export CoreFacts.

  Parameter info_of_ast : ast -> info.
  Parameter denote : ktree insSemE ast unit.
  Parameter decode : mem_slc_val -> option ast.
  (* FIXME: the return type has to also express branches that have no concrete
  value yet. *)
  Parameter next_pc : mem_loc -> ast -> list mem_loc.
End InsSemSig.

Module Type ArcCoreSig.
  Declare Module InsSem : InsSemSig.
  Export InsSem.

  (** InsSem-Thread interface *)

  Parameter mem_read_kind_of_ast : ast -> mem_read_kind.
  Parameter mem_write_kind_of_ast : ast -> mem_write_kind.

  Parameter split_load_mem_slc : ast -> mem_slc -> list mem_slc.
  Parameter split_store_mem_slc_val : ast -> mem_slc -> mem_slc_val ->
                                     list (mem_slc * mem_slc_val).
End ArcCoreSig.

Module ArcCoreFacts (ArcCore : ArcCoreSig).
  Export ArcCore.
  Existing Instance ArcCore.InsSem.Core.showable_mem_read_kind.
  Existing Instance ArcCore.InsSem.Core.showable_mem_write_kind.

  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id;
                  read_footprint : mem_slc;
                  read_kind : mem_read_kind }.

  Record _mem_write : Type :=
    mk_mem_write { write_id : mem_write_id;
                   write_footprint : mem_slc;
                   write_val : mem_slc_val;
                   write_kind : mem_write_kind }.
  Definition mem_write := _mem_write.

  Instance showable_mem_write : Showable mem_write :=
    { show :=
        fun w =>
          (show w.(write_footprint) ++ " = " ++ show (List.rev (List.map Hex w.(write_val))) ++ "(" ++ show w.(write_kind) ++ ")")%string
    }.
  Definition mem_reads_from : Type := list ((thread_id * instruction_id * mem_write_id) *
                                            (mem_slc * mem_slc_val)).

  Variant _storageE : Type -> Type :=
  | StEReadInstruction : mem_loc -> _storageE (mem_slc * mem_reads_from)
  | StERead : mem_read -> (list mem_slc) -> _storageE mem_reads_from
  | StEWrite : mem_write -> _storageE unit.
  Definition storageE := _storageE.
End ArcCoreFacts.

Module Type ArcSig.
  Declare Module Core : ArcCoreSig.
  Module CoreFacts := ArcCoreFacts Core.
  Export CoreFacts.
End ArcSig.

Module Type ThreadSig (Arc : ArcSig).
  Export Arc.

  Parameter state : Type.
  Context `{showable_state: Showable state}.
  Parameter initial_state : instruction_id -> mem_loc -> state.

  Parameter E : Type -> Type.
  Context `{showable_E: forall A, Showable (E A)}.

  Parameter is_eager_event : forall A T, (wrapE E T
                                     +' chooseE mem_read_id
                                     +' chooseE mem_write_id
                                     +' chooseE nat
                                     +' exceptE error
                                     +' debugE) A
                                    -> bool.

  Parameter denote : forall (F : Type -> Type)
                      `{HasChooseIidBool: chooseE (instruction_id * bool) -< F}
                      `{HasWrapE: wrapE E instruction_id -< F}
                      `{HasChooseMemRead: chooseE mem_read_id -< F}
                      `{HasChooseMemWrite: chooseE mem_write_id -< F}
                      `{HasChooseNat: chooseE nat -< F}
                      `{HasError: exceptE error -< F}
                      `{HasDebug: debugE -< F},
      ktree F instruction_id (result unit unit).
  Arguments denote {F HasChooseIidBool HasWrapE HasChooseMemRead HasChooseMemWrite
                      HasChooseNat HasError HasDebug}.

  Parameter handle_E : forall (F : Type -> Type)
                        `{HasStorage: storageE -< F}
                        `{HasState: stateE state -< F}
                        `{HasExceptDisabled: exceptE disabled -< F}
                        `{HasExceptError: exceptE error -< F}
                        `{HasDebug: debugE -< F},
      instruction_id -> E ~> itree F.
  Arguments handle_E {F HasStorage HasState HasExceptDisabled HasExceptError
                        HasDebug}.
End ThreadSig.

Module Type StorageSig (Arc : ArcSig).
  Export Arc.

  Parameter state : Type.
  Context `{showable_state: Showable state}.
  Parameter initial_state : list (thread_id * instruction_id * mem_write) -> state.

  Parameter handle_storageE : forall (E : Type -> Type)
                               `{HasState: stateE state -< E}
                               `{HasExceptDisabled: exceptE disabled -< E}
                               `{HasExceptError: exceptE error -< E},
                             instruction_id -> thread_id ->
                             storageE ~> itree E.
  Arguments handle_storageE {E HasState HasExceptDisabled HasExceptError}.
End StorageSig.
