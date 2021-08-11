From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Strings.String
     Strings.Ascii.

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

  Instance showable_gpr : Showable gpr :=
    { show :=
        fun r =>
          match r with
          | R0 => "X0" | R1 => "X1" | R2 => "X2" | R3 => "X3" | R4 => "X4"
          | R5 => "X5" | R6 => "X6" | R7 => "X7" | R8 => "X8" | R9 => "X9"
          end%string
    }.

  Variant _reg : Type :=
  | GPR : gpr -> _reg
  | PC : _reg.
  Definition reg := _reg.

  Instance showable_reg : Showable reg :=
    { show := fun r => match r with
                    | GPR r => show r
                    | PC => "PC"%string
                    end
    }.
  #[global] Instance decision_reg_eq : forall (m n : reg), Decision (m = n).
  Proof. decision_eq. Qed.

  Definition reg_size (r : reg) : nat :=
    match r with
    | GPR _ => 64
    | PC => 64
    end.

  Variant _mem_read_kind : Type := RKNormal | RKAcquire | RKExclusive | RKAcqExc.
  Definition mem_read_kind := _mem_read_kind.
  Instance showable_mem_read_kind : Showable mem_read_kind :=
    { show :=
        fun r => match r with
              | RKNormal => "normal"
              | RKAcquire => "acq"
              | RKExclusive => "excl"
              | RKAcqExc => "acq+excl"
              end%string
    }.

  Variant _mem_write_kind : Type := WKNormal | WKRelease | WKExclusive | WKRelExc.
  Definition mem_write_kind := _mem_write_kind.
  Instance showable_mem_write_kind : Showable mem_write_kind :=
    { show :=
        fun w => match w with
              | WKNormal => "normal"
              | WKRelease => "rel"
              | WKExclusive => "excl"
              | WKRelExc => "rel+excl"
              end%string
    }.

  Variant operand : Type :=
  | OpGPR : gpr -> operand
  | OpImm : word 64 -> operand.

  Instance showable_operand : Showable operand :=
    { show :=
        fun op =>
          match op with
          | OpGPR r => show r
          | OpImm w => "#" ++ show (Nat.to_uint (wordToNat w))
          end%string
    }.

  Variant log_op : Type := LOAnd | LOXor | LOOr.

  Instance showable_log_op : Showable log_op :=
    { show :=
        fun op =>
          match op with
          | LOAnd => "AND"
          | LOXor => "EOR"
          | LOOr => "ORR"
          end%string
    }.

  Variant MBReqDomain :=
  | MBReqDomain_Nonshareable
  | MBReqDomain_InnerShareable
  | MBReqDomain_OuterShareable
  | MBReqDomain_FullSystem.

  Variant MBReqTypes :=
  | MBReqTypes_Reads
  | MBReqTypes_Writes
  | MBReqTypes_All.

  Definition mem_barrier_kind : Type := MBReqDomain * MBReqTypes.

  Instance showable_mem_barrier_kind : Showable mem_barrier_kind :=
    { show :=
        fun b => match b with
              | (MBReqDomain_FullSystem, MBReqTypes_All)    => "full system, reads and writes"
              | (MBReqDomain_FullSystem, MBReqTypes_Writes) => "full system, writes"
              | (MBReqDomain_FullSystem, MBReqTypes_Reads)  => "full system, reads"
              (* ISH *)
              | (MBReqDomain_InnerShareable, MBReqTypes_All)    => "inner shareable, reads and writes"
              | (MBReqDomain_InnerShareable, MBReqTypes_Writes) => "inner shareable, writes"
              | (MBReqDomain_InnerShareable, MBReqTypes_Reads)  => "inner shareable, reads"
              (* NSH *)
              | (MBReqDomain_Nonshareable, MBReqTypes_All)    => "non-shareable, reads and writes"
              | (MBReqDomain_Nonshareable, MBReqTypes_Writes) => "non-shareable, writes"
              | (MBReqDomain_Nonshareable, MBReqTypes_Reads)  => "non-shareable, reads"
              (* OSH *)
              | (MBReqDomain_OuterShareable, MBReqTypes_All)    => "outer shareable, reads and writes"
              | (MBReqDomain_OuterShareable, MBReqTypes_Writes) => "outer shareable, writes"
              | (MBReqDomain_OuterShareable, MBReqTypes_Reads)  => "outer shareable, reads"
              end%string
    }.


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
  | BranchImm : word 28 -> _ast
  | MovZ : gpr -> word 16 -> _ast
  | DMB : MBReqDomain -> MBReqTypes -> _ast.
  Definition ast := _ast.

  Instance showable_ast : Showable ast :=
    { show :=
        fun a =>
          match a with
          | Nop => "NOP"
          | Load dst addr off =>
            "LDR " ++ show dst ++ ",[" ++ show addr ++ "," ++ show off ++ "]"
          | Store val addr off =>
            "STR " ++ show val ++ ",[" ++ show addr ++ "," ++ show off ++ "]"
          | LogOp op dst lhs rhs =>
            show op ++ " " ++ show dst ++ "," ++ show lhs ++ "," ++ show rhs
          | BranchImm imm =>
            "B #" ++ show (wordToZ imm)
          | MovZ dst imm =>
            "MOVZ " ++ show dst ++ ",#" ++ show (wordToNat imm)
          | DMB dom typ =>
            "DMB " ++ match dom, typ with
                     | MBReqDomain_FullSystem, MBReqTypes_All    => "SY"
                     | MBReqDomain_FullSystem, MBReqTypes_Writes => "ST"
                     | MBReqDomain_FullSystem, MBReqTypes_Reads  => "LD"
                     (* ISH *)
                     | MBReqDomain_InnerShareable, MBReqTypes_All    => "ISH"
                     | MBReqDomain_InnerShareable, MBReqTypes_Writes => "ISHST"
                     | MBReqDomain_InnerShareable, MBReqTypes_Reads  => "ISHLD"
                     (* NSH *)
                     | MBReqDomain_Nonshareable, MBReqTypes_All    => "NSH"
                     | MBReqDomain_Nonshareable, MBReqTypes_Writes => "NSHST"
                     | MBReqDomain_Nonshareable, MBReqTypes_Reads  => "NSHLD"
                     (* OSH *)
                     | MBReqDomain_OuterShareable, MBReqTypes_All    => "OSH"
                     | MBReqDomain_OuterShareable, MBReqTypes_Writes => "OSHST"
                     | MBReqDomain_OuterShareable, MBReqTypes_Reads  => "OSHLD"
                     end
          end%string
    }.

  Module AArch64Notations.
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

    Declare Custom Entry mem_bar_opt.
    Notation "'SY'"     := (MBReqDomain_FullSystem, MBReqTypes_All)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'ST'"     := (MBReqDomain_FullSystem, MBReqTypes_Writes)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'LD'"     := (MBReqDomain_FullSystem, MBReqTypes_Reads)
                             (in custom mem_bar_opt) : a64_scope.
    (* ISH *)
    Notation "'ISH'"    := (MBReqDomain_InnerShareable, MBReqTypes_All)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'ISHST'"  := (MBReqDomain_InnerShareable, MBReqTypes_Writes)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'ISHLD'"  := (MBReqDomain_InnerShareable, MBReqTypes_Reads)
                             (in custom mem_bar_opt) : a64_scope.
    (* NSH *)
    Notation "'NSH'"    := (MBReqDomain_Nonshareable, MBReqTypes_All)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'NSHST'"  := (MBReqDomain_Nonshareable, MBReqTypes_Writes)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'NSHLD'"  := (MBReqDomain_Nonshareable, MBReqTypes_Reads)
                             (in custom mem_bar_opt) : a64_scope.
    (* OSH *)
    Notation "'OSH'"    := (MBReqDomain_OuterShareable, MBReqTypes_All)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'OSHST'"  := (MBReqDomain_OuterShareable, MBReqTypes_Writes)
                             (in custom mem_bar_opt) : a64_scope.
    Notation "'OSHLD'"  := (MBReqDomain_OuterShareable, MBReqTypes_Reads)
                             (in custom mem_bar_opt) : a64_scope.


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

    Notation "'MOVZ' Xd , # i" := (MovZ Xd (natToWord 16 i))
                                    (Xd custom gpr at level 2, at level 10) : a64_scope.

    Notation "'DMB' bar_opt" := (DMB (fst bar_opt) (snd bar_opt))
                                  (bar_opt custom mem_bar_opt at level 2, at level 10) : a64_scope.
  End AArch64Notations.
End AArch64Core.

Module AArch64 <: InsSemSig.
  Module Core := AArch64Core.
  Module CoreFacts :=  InsSemCoreFacts AArch64Core.
  Export CoreFacts.

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
    let empty_info := {| input_regs := nil;
                         output_regs := nil |} in
    match a with

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
      (* FIXME: nia info? *)
      empty_info
    | MovZ dst imm =>
      let oregs := [full_reg_of_reg (GPR dst)] in
      {| input_regs := nil;
         output_regs := oregs |}
    (* Empty Info: *)
    | Nop
    | DMB _ _ => empty_info
    end.

  Definition read_operand (o : operand) : itree insSemE (reg_val _) :=
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

  Definition denote : ktree insSemE ast unit :=
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
           let mem_slc := {| location := MemLoc loc; size := size |} in
           mem_val <- trigger (MemERead mem_slc)
        ;; let reg_val := reg_val_of_mem_slc_val (size * 8) mem_val in
           trigger (RegEWrite dst_slc reg_val)

      | Store val addr off =>
        let addr_slc := full_reg_of_reg (GPR addr) in
        addr_val <- trigger (RegERead addr_slc)
        ;; off_val <- read_operand off
        ;; let loc := nat_of_reg_val (reg_val_add addr_val off_val) in
           let mem_slc := {| location := MemLoc loc; size := 8 |} in
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

      | MovZ dst imm =>
        let dst_slc := {| rs_reg := GPR dst; rs_first_bit := 0;
                          rs_size := 16 + (reg_size (GPR dst) - 16) |} in
        let val := Word.zext imm _ in
        trigger (RegEWrite dst_slc val)

      | DMB dom typ => trigger (BarEMem (dom, typ))
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

    Definition bools_to_bins_32
               (b0 b1 b2 b3 b4 b5 b6 b7
                   b8 b9 b10 b11 b12 b13 b14 b15
                   b16 b17 b18 b19 b20 b21 b22 b23
                   b24 b25 b26 b27 b28 b29 b30 b31 : bool) :=
      let c b := match b with false => 0 | true => 1 end in
      (c b31, c b30, c b29, c b28, c b27, c b26, c b25, c b24,
       c b23, c b22, c b21, c b20, c b19, c b18, c b17, c b16,
       c b15, c b14, c b13, c b12, c b11, c b10, c b9, c b8,
       c b7, c b6, c b5, c b4, c b3, c b2, c b1, c b0).

    Definition bools_to_bins (bs : list bool) : list nat :=
      List.map (fun b => match b with false => 0 | true => 1 end) bs.

    Variant binPat : Type :=
    | BP0
    | BP1
    | BPDontCare.

    Definition binPat_match (a b : binPat) : bool :=
      match a, b with
      | BPDontCare, _
      | _, BPDontCare
      | BP0, BP0
      | BP1, BP1 => true
      | _, _ => false
      end.

    Definition binPat_match_list (ns ms : list binPat) : bool :=
      (List.length ns =? List.length ms) &&
      List.forallb (fun '(n, m) => binPat_match n m) (List.combine ns ms).

    Fixpoint read_binPat (s : string) : list binPat :=
      match s with
      | EmptyString => nil
      | String "0" s => BP0 :: read_binPat s
      | String "1" s => BP1 :: read_binPat s
      | String "?" s => BPDontCare :: read_binPat s
      | String _ s => read_binPat s
      end.

    Definition bools_to_binPats (bs : list bool) : list binPat :=
      List.map (fun b => match b with false => BP0 | true => BP1 end) bs.

    Definition decode (machine_code : mem_slc_val) : option ast :=
      match reg_val_of_mem_slc_val 32 machine_code return option ast with
      | WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7
        (WS b8 (WS b9 (WS b10 (WS b11 (WS b12 (WS b13 (WS b14 (WS b15
        (WS b16 (WS b17 (WS b18 (WS b19 (WS b20 (WS b21 (WS b22 (WS b23
        (WS b24 (WS b25 (WS b26 (WS b27 (WS b28 (WS b29 (WS b30 (WS b31 WO
              ))))))))))))))))))))))))))))))) =>
        (* let '(b31, b30, b29, b28, b27, b26, b25, b24, *)
        (*       b23, b22, b21, b20, b19, b18, b17, b16, *)
        (*       b15, b14, b13, b12, b11, b10, b9, b8, *)
        (*       b7, b6, b5, b4, b3, b2, b1, b0) := *)
        (*     bools_to_bins_32 b0 b1 b2 b3 b4 b5 b6 b7 *)
        (*                      b8 b9 b10 b11 b12 b13 b14 b15 *)
        (*                      b16 b17 b18 b19 b20 b21 b22 b23 *)
        (*                      b24 b25 b26 b27 b28 b29 b30 b31 in *)
        let bs := bools_to_binPats
                    [b31;b30;b29;b28;b27;b26;b25;b24;
                    b23;b22;b21;b20;b19;b18;b17;b16;
                    b15;b14;b13;b12;b11;b10;b9;b8;
                    b7;b6;b5;b4;b3;b2;b1;b0] in
        if binPat_match_list bs (read_binPat "1101010100 0 00 011 0010 0000 000 11111") then
          (* NOP: [1101010100 0 00 011 0010 0000 000 11111] *)
          Some Nop
        else if binPat_match_list bs (read_binPat "11 111 0 00 01 1 ????? 011 0 10 ????? ?????") then
               (* LDR (register) 64-bit, LSL-0: *)
               (*  [1(x=1) 111 0 00 01 1 Rm (option=011) (S=0) 10 Rn Rt] *)
               match decode_reg b20 b19 b18 b17 b16,
                     decode_reg b9 b8 b7 b6 b5,
                     decode_reg b4 b3 b2 b1 b0 with
               | Some Rm, Some Rn, Some Rt => Some (Load Rt Rn (OpGPR Rm))
               | _, _, _ => None
               end
        else if binPat_match_list bs (read_binPat "11 111 0 01 01 ???????????? ????? ?????") then
               (* LDR (immediate) unsigned offset, 64-bit: *)
               (*  [1(x=1) 111 0 01 01 imm12 Rn Rt] *)
               match decode_reg b9 b8 b7 b6 b5,
                     decode_reg b4 b3 b2 b1 b0 with
               | Some Rn, Some Rt =>
                 let imm12 := WS b10 (WS b11 (WS b12 (WS b13 (WS b14 (WS b15 (WS b16 (WS b17
                              (WS b18 (WS b19 (WS b20 (WS b21 WO))))))))))) in
                 let offset := ((zext imm12 _) ^<< 3)%word in
                 Some (Load Rt Rn (OpImm offset))
               | _, _ => None
               end
        else if binPat_match_list bs (read_binPat "11 111 0 00 00 1 ????? 011 0 10 ????? ?????") then
             (* STR (register) 64-bit, LSL-0: *)
             (*  [1(x=1) 111 0 00 00 1 Rm (option=011) (S=0) 10 Rn Rt] *)
               match decode_reg b20 b19 b18 b17 b16,
                     decode_reg b9 b8 b7 b6 b5,
                     decode_reg b4 b3 b2 b1 b0 with
               | Some Rm, Some Rn, Some Rt => Some (Store Rt Rn (OpGPR Rm))
               | _, _, _ => None
               end
        else if binPat_match_list bs (read_binPat "11 111 0 01 00 ???????????? ????? ?????") then
             (* STR (immediate) unsigned offset, 64-bit: *)
             (*  [1(x=1) 111 0 01 00 imm12 Rn Rt] *)
               match decode_reg b9 b8 b7 b6 b5,
                     decode_reg b4 b3 b2 b1 b0 with
               | Some Rn, Some Rt =>
                 let imm12 := WS b10 (WS b11 (WS b12 (WS b13 (WS b14 (WS b15 (WS b16 (WS b17
                              (WS b18 (WS b19 (WS b20 (WS b21 WO))))))))))) in
                 let offset := ((zext imm12 _) ^<< 3)%word in
                 Some (Store Rt Rn (OpImm offset))
               | _, _ => None
               end
        else if binPat_match_list bs (read_binPat "1 ?? 01010 00 0 ????? 000000 ????? ?????") then
             (* AND/EOR/ORR (shifted register), 64-bit, LSL-0: *)
             (*  [(sf=1) opc 01010 (shift=00) (N=0) Rm (imm6=000000) Rn Rd] *)
               match decode_log_op b30 b29,
                     decode_reg b20 b19 b18 b17 b16,
                     decode_reg b9 b8 b7 b6 b5,
                     decode_reg b4 b3 b2 b1 b0 with
               | Some op, Some Rm, Some Rn, Some Rd => Some (LogOp op Rd Rn (OpGPR Rm))
               | _, _, _, _ => None
               end
        (* TODO: AND (immediate), 64-bit: *)
        (*  [(sf=1) 00 100100 N immr imms Rn Rd] *)
        else if binPat_match_list bs (read_binPat "0 00101 ??????????????????????????") then
               (* B: *)
               (*    [(op=0) 00101 imm26] *)
               let imm26 :=
                   WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7
                   (WS b8 (WS b9 (WS b10 (WS b11 (WS b12 (WS b13 (WS b14 (WS b15
                   (WS b16 (WS b17 (WS b18 (WS b19 (WS b20 (WS b21 (WS b22 (WS b23
                   (WS b24 (WS b25 WO))))))))))))))))))))))))) in
               let offset := ((sext imm26 _) ^<< 2)%word in
               Some (BranchImm offset)
        else if binPat_match_list bs (read_binPat "1 10 100101 00 ???????????????? ?????") then
               (* MOVZ, 64-bit: *)
               (*    [(sf=1) (opc=10) 100101 (hw=00) imm16 Rd] *)
               let imm16 :=
                   WS b5 (WS b6 (WS b7 (WS b8 (WS b9 (WS b10 (WS b11 (WS b12
                   (WS b13 (WS b14 (WS b15 (WS b16 (WS b17 (WS b18 (WS b19 (WS b20 WO))))))))))))))) in
               match decode_reg b4 b3 b2 b1 b0 with
               | Some Rd => Some (MovZ Rd imm16)
               | _ => None
               end
        else if binPat_match_list bs (read_binPat "1101010100 0 00 011 0011 ???? 1 01 11111") then
               (* DMB *)
               (*    [1101010100 0 00 011 0011 CRm 1 (opc=01) 11111] *)
               let domain :=
                   if (negb b9 && negb b8)%bool then MBReqDomain_FullSystem
                   else match b11, b10 with
                        | false, false => MBReqDomain_OuterShareable
                        | false, true =>  MBReqDomain_Nonshareable
                        | true, false =>  MBReqDomain_InnerShareable
                        | true, true =>   MBReqDomain_FullSystem
                        end in
               let type := match b9, b8 with
                           | false, false => MBReqTypes_All
                           | false, true  => MBReqTypes_Reads
                           | true, false  => MBReqTypes_Writes
                           | true, true   => MBReqTypes_All
                           end in
               Some (DMB domain type)
        (* FIXME: *)
        else None
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
      | MovZ d imm =>
        let '(Rd4, Rd3, Rd2, Rd1, Rd0) := encode_reg d in
        match imm with
        | WS i0 (WS i1 (WS i2 (WS i3 (WS i4 (WS i5 (WS i6 (WS i7
          (WS i8 (WS i9 (WS i10 (WS i11 (WS i12 (WS i13 (WS i14 (WS i15 WO))))))))))))))) =>
          let w := (WO~ 1 ~ 1~0 ~ 1~0~0~1~0~1 ~  0~0 ~
                      i15~i14~i13~i12~i11~i10~i9~i8~i7~i6~i5~i4~i3~i2~i1~i0 ~
                      Rd4~Rd3~Rd2~Rd1~Rd0)%word in
          Some (encode_word w)
        | _ => None
        end
      | DMB dom typ =>
        let '(CRm3, CRm2) := match dom with
                             | MBReqDomain_OuterShareable => (false, false)
                             | MBReqDomain_Nonshareable   => (false, true)
                             | MBReqDomain_InnerShareable => (true, false)
                             | MBReqDomain_FullSystem     => (true, true)
                             end in
        let '(CRm1, CRm0) := match typ with
                             | MBReqTypes_Reads  => (false, true)
                             | MBReqTypes_Writes => (true, false)
                             | MBReqTypes_All    => (true, true)
                             end in
        let w := (WO~ 1~1~0~1~0~1~0~1~0~0 ~ 0 ~ 0~0 ~ 0~1~1 ~ 0~0~1~1 ~
                    CRm3~CRm2~CRm1~CRm0 ~ 1 ~ 0~1 ~ 1~1~1~1~1)%word in
        Some (encode_word w)
      end.
  End Encode.

  Definition  next_pc (pc : mem_loc) (a : ast) : list mem_loc :=
    match a with
    | BranchImm off =>
      let pc := natToWord 64 (mem_loc_to_nat pc) in
      let new_pc := wordToNat (pc ^+ (sext off _))%word in
      (* FIXME: the [new_pc = 0] case is just to make the thread stop fetching *)
      if decide (new_pc = 0) then nil
      else [MemLoc new_pc]
    | _ => [MemLoc (mem_loc_to_nat pc + 4)]
    end.
End AArch64.

Module Armv8ACore <: ArcCoreSig.
  Module InsSem := AArch64.
  Export InsSem.

  Definition mem_read_kind_of_ast (a : ast) : mem_read_kind :=
    (* FIXME: *)
    RKNormal.

  Definition mem_write_kind_of_ast (a : ast) : mem_write_kind :=
    (* FIXME: *)
    WKNormal.

  Definition split_load_mem_slc (a : ast) (slc : mem_slc)
    : list mem_slc :=
    (* FIXME: *)
    [slc].

  Definition split_store_mem_slc_val (a : ast) (slc : mem_slc) (val : mem_slc_val)
    : list (mem_slc * mem_slc_val) :=
    (* FIXME: *)
    [(slc, val)].
End Armv8ACore.

Module Armv8A <: ArcSig.
  Module Core := Armv8ACore.
  Module CoreFacts :=  ArcCoreFacts Core.
  Export CoreFacts.
End Armv8A.
