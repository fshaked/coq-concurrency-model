From Coq Require Import
     (* Arith.PeanoNat *)
     NArith.NArith
     ZArith.ZArith
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

From bbv Require Import BinNotation.

Require Import Utils Types System
        SimpleA64InsSem FlatThread FlatStorage.

Module Arc := SimpleA64InsSem.Armv8.
Import Arc.
Import AArch64Notations.
Open Scope a64_scope.

Module Thread := FlatThread.Make Arc.
Module Storage := FlatStorage.Make Arc.

Module Model := System.Make Arc Thread Storage.





Definition unsafe_encode a :=
  let bad_encoding : Types.mem_slc_val := [0; 0; 0; 0] in
  match encode a with
  | Some v => v
  | None => bad_encoding
  end.

Definition code_writes (c : list ast) :=
  let '(ws, _, _) :=
      fold_left (fun '(ws, next_wid, next_loc) a =>
                   ((0, 0,
                     {| write_id := next_wid;
                        write_footprint := {| Types.location := next_loc; Types.size := 4 |};
                        write_val := unsafe_encode a ;
                        write_kind := WKNormal |})::ws,
                    next_wid + 1, MemLoc (mem_loc_to_nat next_loc + 4)))
                c
                (nil, 0, MemLoc 4096) in
  ws.

Definition data_writes (ds : list (nat * list nat)) :=
  List.map (fun '(loc, bytes) =>
              (0, 0, {| write_id := 0;
                        write_footprint := {| Types.location := MemLoc loc;
                                              Types.size := List.length bytes |};
                        write_val := List.rev bytes;
                        write_kind := WKNormal |}))
           ds.

Definition run_test (code : list (instruction_id_t * mem_write_id_t * mem_write))
           (bound : nat) : ((_ + _) * _) :=
  Model.exec bound code [MemLoc 4096].

Existing Instance Model.showable_state.

Definition show_state (s : Model.state) :=
  show s.

Definition test_and :=
  code_writes [
      (* [0x1000] *) MOVZ X1, #1234
      (* [0x1004] *) ; AND X0, X1, X2
      (* [0x1008] *) ; B #-4104 (* jump to 0, indicates to the model to stop fetching *)
    ]%a64.

Definition test_str :=
  data_writes [ (5000, [0; 0; 0; 0; 0; 0; 0; 0]) ] ++
  code_writes [ (* [0x1000] *) MOVZ X0,#42
                (* [0x1004] *) ; MOVZ X1,#5000
                (* [0x1008] *) ; STR X0,[X1]
                (* [0x100c] *) ; B #-4108 (* jump to 0, indicates to the model to stop fetching *)
              ]%a64.

Definition test_ldr :=
  data_writes [ (5000, [0; 0; 0; 0; 0; 0; 0; 42]) ] ++
  code_writes [ (* [0x1000] *) MOVZ X0,#5000
                (* [0x1004] *) ; LDR X1,[X0]
                (* [0x1008] *) ; B #-4104 (* jump to 0, indicates to the model to stop fetching *)
              ]%a64.

(* Compute match run_test test_and 5 with inr (_, s) => s | _ => [] end. *)

From Coq Require
     Extraction
     ExtrOcamlBasic
     ExtrOcamlString
     ExtrOcamlNatBigInt
     ExtrOcamlZBigInt
     ExtrOcamlIntConv.

Extraction Language OCaml.
Extraction Blacklist Nat List.
Cd "extracted_ocaml".

Separate Extraction
         ExtrOcamlIntConv.nat_of_int ExtrOcamlIntConv.int_of_nat
         run_test show_state
         test_and test_str test_ldr.

Cd "..".
