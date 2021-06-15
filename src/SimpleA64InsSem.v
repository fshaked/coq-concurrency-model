From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Strings.String.

Import ListNotations.

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

  Variant binop : Type := BOAdd.

  Variant _ast : Type :=
  (* dst, addr, offset : load from memory location `addr + offset` to `dst` *)
  | Load : gpr -> gpr -> operand -> _ast
  (* val, addr, offset : store `val` to memory location `addr + offset` *)
  | Store : operand -> gpr -> operand -> _ast
  (* op, dst, lhs, rhs *)
  | BinOp : binop -> gpr -> gpr -> operand -> _ast.
  Definition ast := _ast.
End AArch64Core.

Module AArch64 <: InsSemSig.
  Module Core := AArch64Core.
  Include Core.
  Include InsSemCoreFacts AArch64Core.

  Definition full_reg_of_reg (r : reg) :=
    (r, (0, reg_size r)).

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
    | BinOp op dst lhs rhs =>
      let iregs := reg_slc_of_operand rhs in
      let iregs := full_reg_of_reg (GPR lhs) :: iregs in
      let iregs := List.map (fun r => (r, false)) iregs in
      let oregs := [full_reg_of_reg (GPR dst)] in
      {| input_regs := iregs;
         output_regs := oregs |}
    end.

  Definition read_operand (o : operand) : itree E reg_val :=
    match o with
    | OpGPR r => trigger (RegERead ((GPR r), (0, reg_size (GPR r))))
    | OpImm i => ret (reg_val_of_nat i)
    end.

  Definition get_binop (op : binop) : reg_val -> reg_val -> reg_val :=
    match op with
    | BOAdd => reg_val_add
    end.

  Definition denote : ktree E ast unit :=
    fun ins =>
      match ins with
      | Load dst addr off =>
        let addr_slc := ((GPR addr), (0, reg_size (GPR addr))) in
        addr_val <- trigger (RegERead addr_slc)
        ;; off_val <- read_operand off
        ;; let loc := nat_of_reg_val (reg_val_add addr_val off_val) in
           let mem_slc := {| location := loc; size := 8 |} in
           mem_val <- trigger (MemERead mem_slc)
        ;; let reg_val := reg_val_of_mem_slc_val mem_val in
           let dst_slc := ((GPR dst), (0, reg_size (GPR dst))) in
           trigger (RegEWrite dst_slc reg_val)
      | Store val addr off =>
        let addr_slc := ((GPR addr), (0, reg_size (GPR addr))) in
        addr_val <- trigger (RegERead addr_slc)
        ;; off_val <- read_operand off
        ;; let loc := nat_of_reg_val (reg_val_add addr_val off_val) in
           let mem_slc := {| location := loc; size := 8 |} in
           'tt <- trigger (MemEWriteFP mem_slc)
        ;; val_val <- read_operand val
        ;; let mem_val := mem_slc_val_of_reg_val val_val 8 in
           trigger (MemEWriteVal mem_val)
      | BinOp op dst lhs rhs =>
        lhsv <- trigger (RegERead ((GPR lhs), (0, reg_size (GPR lhs))))
        ;; rhsv <- read_operand rhs
        ;; let res := get_binop op lhsv rhsv in
           trigger (RegEWrite ((GPR dst), (0, reg_size (GPR dst))) res)
      end.

  Definition decode (machine_code : mem_slc_val) : option ast :=
    match reg_val_of_mem_slc_val machine_code with
    | N0 => None
    (* FIXME: *)
    | Npos (xI (xI xH)) => None
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
