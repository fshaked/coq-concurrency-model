From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Strings.String.

Import ListNotations.

Require Import bbv.Word.
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

Require Import Utils Types.
Require Import Decision.


Module AArch64Core <: InsSemCoreSig.
  Variant gpr : Type :=
  (* GPRs *)
  | R0 | R1 | R2 | R3 | R4
  | R5 | R6 | R7 | R8 | R9.

  #[global] Instance decide_gpr : forall (m n : gpr), Decision (m = n).
  Proof. decision_eq. Qed.

  Variant _reg : Type :=
  | GPR : gpr -> _reg
  | PC : _reg.
  Definition reg := _reg.

  #[global] Instance decide_reg : forall (m n : reg), Decision (m = n).
  Proof. decision_eq. Qed.

  Definition reg_eqb (m n : reg) := isTrue (m = n).

  Definition reg_size (r : reg) :=
    match r with
    | GPR _ => 64
    | PC => 64
    end.

  Variant _mem_read_kind : Type := RKNormal | RKAcquire | RKExclusive | RKAcqExc.
  Definition mem_read_kind := _mem_read_kind.
  Variant _mem_write_kind : Type := WKNormal | WKRelease | WKExclusive | WKRelExc.
  Definition mem_write_kind := _mem_write_kind.

  Variant operand : Type :=
  | OpGPR : gpr -> operand
  | OpImm : nat -> operand.

  Variant log_op : Type := LOAnd | LOXor | LOOr.

  Variant _ast : Type :=
  (* dst, addr, offset : load from memory location `addr + offset` to `dst` *)
  | Load : gpr -> gpr -> operand -> _ast
  (* val, addr, offset : store `val` to memory location `addr + offset` *)
  | Store : operand -> gpr -> operand -> _ast
  (* op, dst, lhs, rhs *)
  | LogOp : log_op -> gpr -> gpr -> operand -> _ast.
  Definition ast := _ast.
End AArch64Core.

Module AArch64 <: InsSemSig.
  Module Core := AArch64Core.
  Include Core.
  Include InsSemCoreFacts AArch64Core.

  Definition full_reg_of_reg (r : reg) : reg_slc :=
    {| rs_reg := r;
       rs_first_bit := 0;
       rs_size := reg_size r |}.

  Definition reg_slc_of_operand (o : operand) : list reg_slc :=
    match o with
    | OpGPR r => [full_reg_of_reg (GPR r)]
    | _ => nil
    end.

  Definition info_of_ast (a : ast) : info :=
    match a with
    | Load dst addr off =>
      let iaregs := reg_slc_of_operand off in
      let iaregs := full_reg_of_reg (GPR addr) :: iaregs in
      let iaregs := List.map (fun r => (r, true)) iaregs in
      let oregs := [full_reg_of_reg (GPR dst)] in
      {| input_regs := iaregs;
         output_regs := oregs |}
    | Store val addr off =>
      let iregs := reg_slc_of_operand val in
      let iregs := List.map (fun r => (r, false)) iregs in
      let iaregs := reg_slc_of_operand off in
      let iaregs := full_reg_of_reg (GPR addr) :: iaregs in
      let iaregs := List.map (fun r => (r, true)) iaregs in
      {| input_regs := iregs ++ iaregs;
         output_regs := nil |}
    | LogOp op dst lhs rhs =>
      let iregs := reg_slc_of_operand rhs in
      let iregs := full_reg_of_reg (GPR lhs) :: iregs in
      let iregs := List.map (fun r => (r, false)) iregs in
      let oregs := [full_reg_of_reg (GPR dst)] in
      {| input_regs := iregs;
         output_regs := oregs |}
    end.

  Definition read_operand (o : operand) : itree E (reg_val _) :=
    match o with
    | OpGPR r => trigger (RegERead (full_reg_of_reg (GPR r)))
    | OpImm i => ret (reg_val_of_nat 64 i)
    end.

  Definition get_log_op {sz} (op : log_op) : reg_val sz -> reg_val sz -> reg_val sz :=
    match op with
    | LOAnd => fun r1 r2 => wand r1 r2
    | LOXor => fun r1 r2 => wxor r1 r2
    | LOOr => fun r1 r2 => wor r1 r2
    end.

  Definition denote : ktree E ast unit :=
    fun ins =>
      match ins with
      | Load dst addr off =>
        let size := 8 in
        let addr_slc := full_reg_of_reg (GPR addr) in
        let dst_slc := {| rs_reg := GPR dst; rs_first_bit := 0; rs_size := size * 8 |} in
        addr_val <- trigger (RegERead addr_slc)
        ;; off_val <- read_operand off
        ;; let loc := nat_of_reg_val (reg_val_add addr_val off_val) in
           let mem_slc := {| location := loc; size := size |} in
           mem_val <- trigger (MemERead mem_slc)
        ;; let reg_val := reg_val_of_mem_slc_val (size * 8) mem_val in
           trigger (RegEWrite dst_slc reg_val)
      | Store val addr off =>
        let addr_slc := full_reg_of_reg (GPR addr) in
        addr_val <- trigger (RegERead addr_slc)
        ;; off_val <- read_operand off
        ;; let loc := nat_of_reg_val (reg_val_add addr_val off_val) in
           let mem_slc := {| location := loc; size := 8 |} in
           'tt <- trigger (MemEWriteFP mem_slc)
        ;; val_val <- read_operand val
        ;; let mem_val := mem_slc_val_of_reg_val val_val in
           trigger (MemEWriteVal mem_val)
      | LogOp op dst lhs rhs =>
        lhsv <- trigger (RegERead (full_reg_of_reg (GPR lhs)))
        ;; rhsv <- read_operand rhs
        ;; let res := get_log_op op lhsv rhsv in
           trigger (RegEWrite (full_reg_of_reg (GPR dst)) res)
      end.

  Definition decode_reg (b4 b3 b2 b1 b0 : bool) : option gpr :=
    List.nth_error
      [R0; R1; R2; R3; R4; R5; R6; R7; R8; R9]
      (wordToNat (WS b0 (WS b1 (WS b2 (WS b3 (WS b4 WO)))))).

  Definition decode_log_op (b1 b0 : bool) : option log_op :=
    match b1, b0 with
    | false, false => Some LOAnd
    | false, true => Some LOOr
    | true, false => Some LOXor
    | _, _ => None
    end.

  Notation "w '~' b" := (WS b w) (at level 7, left associativity, format "w '~' b") : word_scope.

  Definition decode (machine_code : mem_slc_val) : option ast :=
    match reg_val_of_mem_slc_val 32 machine_code with
    (* LDR (register) 64-bit, LSL-0:
       [1(x=1) 111 0 00 01 1 Rm (option=011) (S=0) 10 Rn Rt] *)
    | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~0 ~ 0~1 ~ 1 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~1~1 ~ 0
         ~ 1~0 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
      match decode_reg Rm4 Rm3 Rm2 Rm1 Rm0,
            decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
            decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
      | Some Rm, Some Rn, Some Rt => Some (Load Rt Rn (OpGPR Rm))
      | _, _, _ => None
      end
    (* LDR (immediate) unsigned offset, 64-bit:
       [1(x=1) 111 0 01 01 imm12 Rn Rt] *)
    | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~1 ~ 0~1 ~ i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0
         ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
      match decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
            decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
      | Some Rn, Some Rt =>
        let imm12 := WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
                     (WS i8 (WS i9 (WS i10 (WS i11 WO))))))))))) in
        let offset := wordToNat (imm12 ^<< 3) in
        Some (Load Rt Rn (OpImm offset))
      | _, _ => None
      end
    (* STR (register) 64-bit, LSL-0:
       [1(x=1) 111 0 00 00 1 Rm (option=011) (S=0) 10 Rn Rt] *)
    | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~0 ~ 0~0 ~ 1 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~1~1 ~ 0
         ~ 1~0 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
      match decode_reg Rm4 Rm3 Rm2 Rm1 Rm0,
            decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
            decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
      | Some Rm, Some Rn, Some Rt => Some (Store (OpGPR Rt) Rn (OpGPR Rm))
      | _, _, _ => None
      end
    (* STR (immediate) unsigned offset, 64-bit:
       [1(x=1) 111 0 01 00 imm12 Rn Rt] *)
    | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~1 ~ 0~0 ~ i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0
         ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
      match decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
            decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
      | Some Rn, Some Rt =>
        let imm12 := WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
                     (WS i8 (WS i9 (WS i10 (WS i11 WO))))))))))) in
        let offset := wordToNat (imm12 ^<< 3) in
        Some (Store (OpGPR Rt) Rn (OpImm offset))
      | _, _ => None
      end
    (* AND/EOR/ORR (shifted register), 64-bit, LSL-0:
       [(sf=1) opc 01010 (shift=00) (N=0) Rm (imm6=000000) Rn Rd] *)
    | (WO~ opc1~opc0 ~ 0~1~0~1~0 ~ 0~0 ~ 0 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~0~0~0~0~0
         ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rd4~Rd3~Rd2~Rd1~Rd0)%word =>
      match decode_log_op opc1 opc0,
            decode_reg Rm4 Rm3 Rm2 Rm1 Rm0,
            decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
            decode_reg Rd4 Rd3 Rd2 Rd1 Rd0 with
      | Some op, Some Rm, Some Rn, Some Rd => Some (LogOp op Rd Rn (OpGPR Rm))
      | _, _, _, _ => None
      end


    (* TODO: AND (immediate), 64-bit:
       [(sf=1) 00 100100 N immr imms Rn Rd] *)
    (* FIXME: *)
    | _ => None
    end.

  Definition  next_pc (pc : mem_loc) (a : ast) : list mem_loc := [pc + 4].
End AArch64.

Module Armv8Core : ArcCoreSig.
  Module InsSem := AArch64.

  Definition mem_read_kind_of_ast (a : InsSem.ast) : InsSem.mem_read_kind :=
    (* FIXME: *)
    InsSem.RKNormal.

  Definition mem_write_kind_of_ast (a : InsSem.ast) : InsSem.mem_write_kind :=
    (* FIXME: *)
    InsSem.WKNormal.

  Definition split_load_mem_slc (a : InsSem.ast) (slc : mem_slc)
    : list mem_slc :=
    (* FIXME: *)
    [slc].

  Definition split_store_mem_slc_val (a : InsSem.ast) (slc : mem_slc) (val : mem_slc_val)
    : list (mem_slc * mem_slc_val) :=
    (* FIXME: *)
    [(slc, val)].
End Armv8Core.

Module Armv8 : ArcSig.
  Module Core := Armv8Core.
  Include Core.
  Include ArcCoreFacts Core.
End Armv8.
