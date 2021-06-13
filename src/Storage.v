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

Require Import Utils Types.
(* Require Import Thread. *)

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.
(* Local Open Scope monad_scope. *)

Module Make (Arc : ArcSig).
  (* `mem` is a map from byte locations to byte values *)
  Record state := mk_state { mem : list (thread_id_t * instruction_id_t * Arc.mem_write) }.
  Instance eta_state : Settable _ := settable! mk_state <mem>.

  Definition initial_state (mem : list (thread_id_t * instruction_id_t * Arc.mem_write))
    : state :=
    {| mem := mem |}.


  Definition get_slc_val (slc : mem_slc) (s : state) : option mem_slc_val :=
    flatten_mem_slc_vals slc (List.map (fun '(_, _, w) =>
                                          (w.(Arc.write_footprint), w.(Arc.write_val)))
                                       s.(mem)).

  Definition read_instruction (loc : mem_loc) (s : state) : option mem_slc_val :=
    (* TODO: don't assume all instructions are 4 bytes *)
    let ins_size := 4 in
    get_slc_val {| location := loc; size := ins_size |} s.

  Definition read
             (slc : mem_slc) (s : state) : option mem_slc_val :=
    get_slc_val slc s.

  Definition write (w : mem_write) (tid : thread_id_t) (iid : instruction_id_t) (s : state) : state :=
             (slc : mem_slc) (val : mem_slc_val) (tid : thread_id_t)
             (iid : instruction_id_t) (wid : mem_write_id_t) (s : state) : state :=
    s <| mem :=

End Make.
