From Coq Require Import
     Arith
     NArith.NArith
     Lists.List
     Lists.ListSet
     Strings.String
     Morphisms
     Setoid
     RelationClasses .

From ExtLib Require Import
     Structures.Monads
     Data.Monads.ListMonad.
(*      Data.String *)
(*      Structures.Traversable *)
(*      Data.List. *)

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
     Events.State.

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Import ListMonad.
Import ITreeNotations.
Import Monads.
Import MonadNotation.
Import ListNotations.

Require Import Utils Types.

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

  Definition try_read_instruction {E}
             (* `{exceptE disabled -< E} *)
             `{exceptE error -< E}
             (loc : mem_loc) (s : state)
    : itree E (state * (mem_slc * Arc.mem_reads_from)) :=
    (* TODO: don't assume all instructions are 4 bytes *)
    let ins_size := 4 in
    let slc := {| location := loc; size := ins_size |} in
    rf <- try_unwrap_option (get_slc_val slc s)
                           "try_read_instruction: no value in memory"
    ;; ret (s, (slc, rf)).

  Definition read
             (slc : mem_slc) (s : state) : option Arc.mem_reads_from :=
    get_slc_val slc s.

  Definition write (w : Arc.mem_write) (tid : thread_id_t)
             (iid : instruction_id_t) (s : state) : state :=
    s <| mem := (tid, iid, w)::s.(mem) |>.

  Definition handle_storageE {E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
             (iid : instruction_id_t) (tid : thread_id_t)
    : Arc.storageE ~> stateT state (itree E) :=
    fun _ e s =>
      match e with
      | Arc.StEReadInstruction pc => try_read_instruction pc s
      | Arc.StERead read uslcs => Ret (s, [])
      | Arc.StEWrite write => Ret (s, tt)
      end.

End Make.
