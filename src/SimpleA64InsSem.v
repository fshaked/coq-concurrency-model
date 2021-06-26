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

  #[global] Instance decision_gpr_eq : forall (m n : gpr), Decision (m = n).
  Proof. decision_eq. Qed.

  Variant _reg : Type :=
  | GPR : gpr -> _reg
  | PC : _reg.
  Definition reg := _reg.

  #[global] Instance decision_reg_eq : forall (m n : reg), Decision (m = n).
  Proof. decision_eq. Qed.

  Definition reg_size (r : reg) : nat :=
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
  | OpImm : word 64 -> operand.

  Variant log_op : Type := LOAnd | LOXor | LOOr.

  Variant _ast : Type :=
  (* NOP *)
  | Nop : _ast
  (* dst, addr, offset : load from memory location `addr + offset` to `dst` *)
  | Load : gpr -> gpr -> operand -> _ast
  (* val, addr, offset : store `val` to memory location `addr + offset` *)
  | Store : gpr -> gpr -> operand -> _ast
  (* op, dst, lhs, rhs *)
  | LogOp : log_op -> gpr -> gpr -> operand -> _ast
  (* offset *)
  | BranchImm : word 28 -> _ast.
  Definition ast := _ast.

  Module Notations.
    Declare Scope a64_scope.
    Delimit Scope a64_scope with a64.

    Declare Custom Entry gpr.
    Notation "'X0'" := R0 (in custom gpr) : a64_scope.
    Notation "'X1'" := R1 (in custom gpr) : a64_scope.
    Notation "'X2'" := R2 (in custom gpr) : a64_scope.
    Notation "'X3'" := R3 (in custom gpr) : a64_scope.
    Notation "'X4'" := R4 (in custom gpr) : a64_scope.
    Notation "'X5'" := R5 (in custom gpr) : a64_scope.
    Notation "'X6'" := R6 (in custom gpr) : a64_scope.
    Notation "'X7'" := R7 (in custom gpr) : a64_scope.
    Notation "'X8'" := R8 (in custom gpr) : a64_scope.
    Notation "'X9'" := R9 (in custom gpr) : a64_scope.

    Declare Custom Entry log_op.
    Notation "'AND'" := LOAnd (in custom log_op) : a64_scope.
    Notation "'EOR'" := LOXor (in custom log_op) : a64_scope.
    Notation "'ORR'" := LOOr (in custom log_op) : a64_scope.

    Notation "'NOP'" := Nop (at level 10) : a64_scope.

    Notation "'LDR' Xt , [ Xn ]" := (Load Xt Xn (OpImm (natToWord 64 0)))
                                      (Xt custom gpr at level 2,
                                       Xn custom gpr at level 2, at level 10)
                                    : a64_scope.

    Notation "'LDR' Xt , [ Xn , # o ]" := (Load Xt Xn (OpImm (natToWord 64 o)))
                                            (Xt custom gpr at level 2,
                                             Xn custom gpr at level 2, at level 10)
                                          : a64_scope.

    Notation "'LDR' Xt , [ Xn , Xm ]" := (Load Xt Xn (OpGPR Xm))
                                           (Xt custom gpr at level 2,
                                            Xn custom gpr at level 2,
                                            Xm custom gpr at level 2, at level 10)
                                         : a64_scope.

    Notation "'STR' Xt , [ Xn ]" := (Store Xt Xn (OpImm (natToWord 64 0)))
                                      (Xt custom gpr at level 2,
                                       Xn custom gpr at level 2, at level 10)
                                    : a64_scope.

    Notation "'STR' Xt , [ Xn , # o ]" := (Store Xt Xn (OpImm (natToWord 64 o)))
                                            (Xt custom gpr at level 2,
                                             Xn custom gpr at level 2, at level 10)
                                          : a64_scope.

    Notation "'STR' Xt , [ Xn , Xm ]" := (Store Xt Xn (OpGPR Xm))
                                           (Xt custom gpr at level 2,
                                            Xn custom gpr at level 2,
                                            Xm custom gpr at level 2, at level 10)
                                         : a64_scope.

    Notation "LOp Xd , Xn , Xm" := (LogOp LOp Xd Xn (OpGPR Xm))
                                     (LOp custom log_op at level 2,
                                      Xd custom gpr at level 2,
                                      Xn custom gpr at level 2,
                                      Xm custom gpr at level 2, at level 10)
                                   : a64_scope.

    Notation "'B' # o" := (BranchImm (ZToWord 28 o))
                            (at level 10) : a64_scope.
  End Notations.
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
    | Nop =>
      {| input_regs := nil;
         output_regs := nil |}
    | Load dst addr off =>
      let iaregs := reg_slc_of_operand off in
      let iaregs := full_reg_of_reg (GPR addr) :: iaregs in
      let iaregs := List.map (fun r => (r, true)) iaregs in
      let oregs := [full_reg_of_reg (GPR dst)] in
      {| input_regs := iaregs;
         output_regs := oregs |}
    | Store val addr off =>
      let iregs := [full_reg_of_reg (GPR val)] in
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
    | BranchImm off =>
      {| input_regs := nil;
         output_regs := nil |}
    end.

  Definition read_operand (o : operand) : itree E (reg_val _) :=
    match o with
    | OpGPR r => trigger (RegERead (full_reg_of_reg (GPR r)))
    | OpImm i => Ret i
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
      | Nop => Ret tt
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
        ;; let val_slc := full_reg_of_reg (GPR val) in
           val_val <- trigger (RegERead val_slc)
        ;; let mem_val := mem_slc_val_of_reg_val val_val in
           trigger (MemEWriteVal mem_val)
      | LogOp op dst lhs rhs =>
        lhsv <- trigger (RegERead (full_reg_of_reg (GPR lhs)))
        ;; rhsv <- read_operand rhs
        ;; let res := get_log_op op lhsv rhsv in
           trigger (RegEWrite (full_reg_of_reg (GPR dst)) res)
      | BranchImm off =>
        (* FIXME: *)
        Ret tt
      end.

  Notation "w '~' b" := (WS b w) (at level 7, left associativity, format "w '~' b") : word_scope.

  Section Decode.
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


    Definition decode (machine_code : mem_slc_val) : option ast :=
      match reg_val_of_mem_slc_val 32 machine_code with
      (* NOP: [1101010100 0 00 011 0010 0000 000 11111] *)
      | (WO~ 1~1~0~1~0~1~0~1~0~0 ~ 0 ~ 0~0 ~ 0~1~1 ~ 0~0~1~0 ~ 0~0~0~0 ~
           0~0~0 ~ 1~1~1~1~1)%word => Some Nop
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
      (* LDR (immediate) unsigned offset, 64-bit: *)
      (*  [1(x=1) 111 0 01 01 imm12 Rn Rt] *)
      | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~1 ~ 0~1 ~ i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0
           ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
        match decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
              decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
        | Some Rn, Some Rt =>
          let imm12 := WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
                      (WS i8 (WS i9 (WS i10 (WS i11 WO))))))))))) in
          let offset := ((zext imm12 _) ^<< 3)%word in
          Some (Load Rt Rn (OpImm offset))
        | _, _ => None
        end
      (* STR (register) 64-bit, LSL-0: *)
      (*  [1(x=1) 111 0 00 00 1 Rm (option=011) (S=0) 10 Rn Rt] *)
      | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~0 ~ 0~0 ~ 1 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~1~1 ~ 0
           ~ 1~0 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
        match decode_reg Rm4 Rm3 Rm2 Rm1 Rm0,
              decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
              decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
        | Some Rm, Some Rn, Some Rt => Some (Store Rt Rn (OpGPR Rm))
        | _, _, _ => None
        end
      (* STR (immediate) unsigned offset, 64-bit: *)
      (*  [1(x=1) 111 0 01 00 imm12 Rn Rt] *)
      | (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~1 ~ 0~0 ~ i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0
           ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word =>
        match decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
              decode_reg Rt4 Rt3 Rt2 Rt1 Rt0 with
        | Some Rn, Some Rt =>
          let imm12 := WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
                       (WS i8 (WS i9 (WS i10 (WS i11 WO))))))))))) in
          let offset := ((zext imm12 _) ^<< 3)%word in
          Some (Store Rt Rn (OpImm offset))
        | _, _ => None
        end
      (* AND/EOR/ORR (shifted register), 64-bit, LSL-0: *)
      (*  [(sf=1) opc 01010 (shift=00) (N=0) Rm (imm6=000000) Rn Rd] *)
      | (WO~ 1 ~ opc1~opc0 ~ 0~1~0~1~0 ~ 0~0 ~ 0 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~0~0~0~0~0
           ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rd4~Rd3~Rd2~Rd1~Rd0)%word =>
        match decode_log_op opc1 opc0,
              decode_reg Rm4 Rm3 Rm2 Rm1 Rm0,
              decode_reg Rn4 Rn3 Rn2 Rn1 Rn0,
              decode_reg Rd4 Rd3 Rd2 Rd1 Rd0 with
        | Some op, Some Rm, Some Rn, Some Rd => Some (LogOp op Rd Rn (OpGPR Rm))
        | _, _, _, _ => None
        end
      (* TODO: AND (immediate), 64-bit: *)
      (*  [(sf=1) 00 100100 N immr imms Rn Rd] *)
      (* B: *)
      (*    [(op=0) 00101 imm26] *)
      | (WO~ 0 ~ 0~0~1~0~1 ~ i25~i24~i23~i22~i21~i20~
           i19~i18~i17~i16~i15~i14~i13~i12~i11~i10~
           i9~i8~i7~i6~i5~i4~i3~i2~i1~i0)%word =>
        let imm26 :=
            WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
            (WS i8 (WS i9 (WS i10 (WS i11 (WS i12 (WS i13 (WS i14 (WS i15
            (WS i16 (WS i17 (WS i18 (WS i19 (WS i20 (WS i21 (WS i22 (WS i23
            (WS i24 (WS i25 WO))))))))))))))))))))))))) in
        let offset := ((sext imm26 _) ^<< 2)%word in
        Some (BranchImm offset)
      (* FIXME: *)
      | _ => None
      end.
  End Decode.

  Section Encode.
    Definition encode_word (w : word 32) : mem_slc_val :=
      let b0 := split1 8 _ w in
      let w := split2 8 _ w in
      let b1 := split1 8 _ w in
      let w := split2 8 _ w in
      let b2 := split1 8 _ w in
      let w := split2 8 _ w in
      let b3 := split1 8 _ w in
      [wordToNat b0; wordToNat b1; wordToNat b2; wordToNat b3].

    Definition encode_reg (r : gpr) : bool * bool * bool * bool * bool :=
      let i := match r with
               | R0 => 0
               | R1 => 1
               | R2 => 2
               | R3 => 3
               | R4 => 4
               | R5 => 5
               | R6 => 6
               | R7 => 7
               | R8 => 8
               | R9 => 9
               end in
      match natToWord 5 i with
      | (WO~b4~b3~b2~b1~b0)%word => (b4, b3, b2, b1, b0)
      | _ => (false, false, false, false, false) (* This case is not reachable *)
      end.

    Definition encode_log_op (o : log_op) : bool * bool :=
      let i := match o with
               | LOAnd => 0
               | LOOr => 1
               | LOXor => 2
               end in
      match natToWord 2 i with
      | (WO~b1~b0)%word => (b1, b0)
      | _ => (false, false) (* This case is not reachable *)
      end.

    Definition encode (a : ast) : option mem_slc_val :=
      match a with
      | Nop =>
        let w :=
            (WO~ 1~1~0~1~0~1~0~1~0~0 ~ 0 ~ 0~0 ~ 0~1~1 ~ 0~0~1~0 ~ 0~0~0~0 ~
               0~0~0 ~ 1~1~1~1~1)%word in
        Some (encode_word w)

      | Load t n (OpGPR m) =>
        let '(Rt4, Rt3, Rt2, Rt1, Rt0) := encode_reg t in
        let '(Rn4, Rn3, Rn2, Rn1, Rn0) := encode_reg n in
        let '(Rm4, Rm3, Rm2, Rm1, Rm0) := encode_reg m in
        let w :=
            (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~0 ~ 0~1 ~ 1 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~1~1 ~ 0
               ~ 1~0 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word in
        Some (encode_word w)

      | Load t n (OpImm i) =>
        let '(Rt4, Rt3, Rt2, Rt1, Rt0) := encode_reg t in
        let '(Rn4, Rn3, Rn2, Rn1, Rn0) := encode_reg n in
        match split1 15 _ i with
        | WS false (WS false (WS false (WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
          (WS i8 (WS i9 (WS i10 (WS i11 WO)))))))))))))) =>
          let w :=
              (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~1 ~ 0~1 ~ i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0
                 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word in
          Some (encode_word w)
        | _ => None
        end

      | Store t n (OpGPR m) =>
        let '(Rt4, Rt3, Rt2, Rt1, Rt0) := encode_reg t in
        let '(Rn4, Rn3, Rn2, Rn1, Rn0) := encode_reg n in
        let '(Rm4, Rm3, Rm2, Rm1, Rm0) := encode_reg m in
        let w :=
            (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~0 ~ 0~0 ~ 1 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~1~1 ~ 0
               ~ 1~0 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word in
        Some (encode_word w)


      | Store t n (OpImm i) =>
        let '(Rt4, Rt3, Rt2, Rt1, Rt0) := encode_reg t in
        let '(Rn4, Rn3, Rn2, Rn1, Rn0) := encode_reg n in
        match split1 15 _ i with
        | WS false (WS false (WS false (WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
          (WS i8 (WS i9 (WS i10 (WS i11 WO)))))))))))))) =>
          let w :=
              (WO~ 1~1 ~ 1~1~1 ~ 0 ~ 0~1 ~ 0~0 ~ i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0
                 ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rt4~Rt3~Rt2~Rt1~Rt0)%word in
          Some (encode_word w)
        | _ => None
        end

      | LogOp op d n (OpGPR m) =>
        let '(opc1, opc0) := encode_log_op op in
        let '(Rd4, Rd3, Rd2, Rd1, Rd0) := encode_reg d in
        let '(Rn4, Rn3, Rn2, Rn1, Rn0) := encode_reg n in
        let '(Rm4, Rm3, Rm2, Rm1, Rm0) := encode_reg m in
        let w :=
            (WO~ 1 ~ opc1~opc0 ~ 0~1~0~1~0 ~ 0~0 ~ 0 ~ Rm4~Rm3~Rm2~Rm1~Rm0 ~ 0~0~0~0~0~0
               ~ Rn4~Rn3~Rn2~Rn1~Rn0 ~ Rd4~Rd3~Rd2~Rd1~Rd0)%word in
        Some (encode_word w)

      | LogOp op d n (OpImm i) => (* FIXME: *) None

      | BranchImm imm =>
        match split1 28 _ imm with
        | WS false (WS false (WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
          (WS i8 (WS i9 (WS i10 (WS i11 (WS i12 (WS i13 (WS i14 (WS i15
          (WS i16 (WS i17 (WS i18 (WS i19 (WS i20 (WS i21 (WS i22 (WS i23
          (WS i24 (WS i25 WO))))))))))))))))))))))))))) =>
          let w := (WO~ 0 ~ 0~0~1~0~1 ~ i25~i24~i23~i22~i21~i20~
                      i19~i18~i17~i16~i15~i14~i13~i12~i11~i10~
                      i9~i8~i7~i6~i5~i4~i3~i2~i1~i0)%word in
          Some (encode_word w)
        | _ => None
        end
      end.
  End Encode.

  Definition  next_pc (pc : mem_loc) (a : ast) : list mem_loc :=
    match a with
    | BranchImm off =>
      let pc := natToWord 64 pc in
      let new_pc := wordToNat (pc ^+ (sext off _))%word in
      (* FIXME: the [new_pc = 0] case is just to make the thread stop fetching *)
      if decide (new_pc = 0) then nil
      else [new_pc]
    | _ => [pc + 4]
    end.
End AArch64.

Module Armv8Core <: ArcCoreSig.
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

Module Armv8 <: ArcSig.
  Module Core := Armv8Core.
  Include Core.
  Include ArcCoreFacts Core.
End Armv8.
