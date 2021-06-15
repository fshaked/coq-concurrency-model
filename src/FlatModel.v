From Coq Require Import
     (* Arith.PeanoNat *)
     (* NArith.NArith *)
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

Require Import Utils Types System
        SimpleA64InsSem FlatThread FlatStorage.

Module Arc := SimpleA64InsSem.Armv8.
Module Thread := FlatThread.Make Arc.
Module Storage := FlatStorage.Make Arc.

Module Model := System.Make Arc Thread Storage.
