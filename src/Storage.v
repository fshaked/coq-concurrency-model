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
Import RecordSetNotations.

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


  Definition get_slc_val (slc : mem_slc) (s : state) : option Arc.mem_reads_from :=
    let '(uslcs, rf) :=
        reads_from (fun '(tid, iid, wid) '(tid', iid', wid') =>
                      (Nat.eqb tid tid' && Nat.eqb iid iid' && Nat.eqb wid wid')%bool)
                   (List.map (fun '(tid, iid, w) =>
                                ((tid, iid, w.(Arc.write_id)),(w.(Arc.write_footprint), w.(Arc.write_val))))
                             s.(mem))
                   [slc] [] in
    match uslcs with
    | nil => Some rf
    | _ => None
    end.

  Definition read_instruction (loc : mem_loc) (s : state) : option Arc.mem_reads_from :=
    (* TODO: don't assume all instructions are 4 bytes *)
    let ins_size := 4 in
    get_slc_val {| location := loc; size := ins_size |} s.

  Definition read
             (slc : mem_slc) (s : state) : option Arc.mem_reads_from :=
    get_slc_val slc s.

  Definition write (w : Arc.mem_write) (tid : thread_id_t)
             (iid : instruction_id_t) (s : state) : state :=
    s <| mem := (tid, iid, w)::s.(mem) |>.
End Make.
