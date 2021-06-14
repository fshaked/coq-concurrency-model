From Coq Require Import
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

Module Make (Arc : ArcSig).
  (* `mem` is a map from byte locations to byte values *)
  Record state := mk_state { mem : list (thread_id_t * instruction_id_t * Arc.mem_write) }.
  Instance eta_state : Settable _ := settable! mk_state <mem>.

  Definition initial_state (mem : list (thread_id_t * instruction_id_t * Arc.mem_write))
    : state :=
    {| mem := mem |}.

  Definition get_slcs_val (slcs : list mem_slc) (s : state) : option Arc.mem_reads_from :=
    let '(uslcs, rf) :=
        reads_from (fun ids ids' => isTrue (ids = ids'))
                   (List.map (fun '(tid, iid, w) =>
                                ((tid, iid, w.(Arc.write_id)),(w.(Arc.write_footprint), w.(Arc.write_val))))
                             s.(mem))
                   slcs [] in
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
    rf <- try_unwrap_option (get_slcs_val [slc] s)
                           "try_read_instruction: no value in memory"
    ;; ret (s, (slc, rf)).

  Definition try_read {E}
             (* `{exceptE disabled -< E} *)
             `{exceptE error -< E}
             (r : Arc.mem_read) (slcs : list mem_slc) (s : state)
    : itree E (state * Arc.mem_reads_from) :=
    rf <- try_unwrap_option (get_slcs_val slcs s)
                           "try_read: no value in memory"
    ;; ret (s, rf).

  Definition try_write {E}
             (* `{exceptE disabled -< E} *)
             (* `{exceptE error -< E} *)
             (tid : thread_id_t) (iid : instruction_id_t)
             (w : Arc.mem_write) (s : state)
    : itree E (state * unit) :=
    Ret (s <| mem := (tid, iid, w)::s.(mem) |>, tt).

  Definition handle_storageE {E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
             (iid : instruction_id_t) (tid : thread_id_t)
    : Arc.storageE ~> stateT state (itree E) :=
    fun _ e s =>
      match e with
      | Arc.StEReadInstruction pc => try_read_instruction pc s
      | Arc.StERead read uslcs => try_read read uslcs s
      | Arc.StEWrite write => try_write tid iid write s
      end.
End Make.
