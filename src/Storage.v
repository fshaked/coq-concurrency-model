From Coq Require Import
     Arith
     NArith.NArith
     Lists.List
     Lists.ListSet
     (* Strings.String *)
     Morphisms
     Setoid
     RelationClasses .

From ExtLib Require Import
     Structures.Monads
     Data.Monads.ListMonad.
(*      Data.String *)
(*      Structures.Traversable *)
(*      Data.List. *)

From RecordUpdate Require Import RecordSet.

Import ListMonad.
Import Monads.
Import MonadNotation.
Import ListNotations.

Require Import Utils.
Require Import Types.
Require Import Thread.

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.
(* Local Open Scope monad_scope. *)

Module State (Arc : ArcSig).
  (* `mem` is a map from byte locations to byte values *)
  Record state := mk_state { mem : Arc.mem_loc -> option Arc.mem_slc_val }.
  Instance eta_state : Settable _ := settable! mk_state <mem>.

  Definition initial_state (mem : Arc.mem_loc -> option Arc.mem_slc_val) : state :=
    {| mem := mem |}.

  (* Head of `svs` is most significant *)
  Definition combine_values (svs : list (nat * option Arc.mem_slc_val))
    : option (nat * Arc.mem_slc_val) :=
    List.fold_left
        (fun acc sv =>
           match acc, sv with
           | Some (acc_size, acc_val), (size, Some val) =>
             Some (acc_size + size, acc_val * (2 ^ (8 * size)) + val)
           | _, _ => None
           end)
        svs
        (Some (0, 0)).

  Definition get_slc (slc : Arc.mem_slc) (s : state) : option (nat * Arc.mem_slc_val) :=
    let bytes := List.map (fun o => (1, s.(mem) (slc.(Arc.location) + o)))
                          (List.seq 0 slc.(Arc.size)) in
    combine_values
      (* TODO: the `rev` is because we assume little-endianness *)
      (List.rev bytes).

  Definition read_instruction (loc : Arc.mem_loc) (s : state) : option (nat * Arc.mem_slc_val) :=
    (* TODO: we assume all instructions are 4 bytes *)
    let ins_size := 4 in
    get_slc ({| Arc.location := loc; Arc.size := ins_size |}) s.

End State.
