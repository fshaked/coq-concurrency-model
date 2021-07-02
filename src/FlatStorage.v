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

Module Make (Arc : ArcSig) : StorageSig Arc.
  Export Arc.

  Record _state := mk_state { mem : list (thread_id_t * instruction_id_t * mem_write) }.
  (* Workaround: parameter can't be instantiated by an inductive type *)
  Definition state := _state.

  Instance eta_state : Settable _ := settable! mk_state <mem>.

  Definition initial_state (mem : list (thread_id_t * instruction_id_t * mem_write))
    : state :=
    {| mem := mem |}.

  Local Instance slice_prod_r {T S} `{Slice S} : Slice (T * S) :=
    { start := fun '(_, s) => Utils.start s;
      size := fun '(_, s) => Utils.size s;
      sub_slice := fun '(v, s) start size =>
                     match sub_slice s start size with
                     | Some s' => Some (v, s')
                     | None => None
                     end }.

  Definition get_slcs_val (slcs : list mem_slc) (s : state) : option mem_reads_from :=
    match
      Utils.reads_from_slcs
        (List.map (fun '(tid, iid, w) =>
                     ((tid, iid, w.(write_id)),(w.(write_footprint), w.(write_val))))
                  s.(mem))
        slcs [] with
    | Some (rf, nil) => Some rf
    | Some (_, _) => (* TODO: accessing unallocated mem? *) None
    | None => None
    end.

  Definition try_read_instruction {E}
             `{stateE state -< E}
             (* `{exceptE disabled -< E} *)
             `{exceptE error -< E}
             (loc : mem_loc)
    : itree E (mem_slc * mem_reads_from) :=
    (* TODO: don't assume all instructions are 4 bytes *)
    let ins_size := 4 in
    let slc := {| location := loc; size := ins_size |} in
    s <- get
    ;; rf <- try_unwrap_option (get_slcs_val [slc] s)
                              ("try_read_instruction: no value in memory location '" ++ show loc ++ "'")
    ;; ret (slc, rf).

  Definition try_read {E}
             `{stateE state -< E}
             (* `{exceptE disabled -< E} *)
             `{exceptE error -< E}
             (r : mem_read) (slcs : list mem_slc)
    : itree E mem_reads_from :=
    s <- get
    ;; rf <- try_unwrap_option (get_slcs_val slcs s)
                              "try_read: no value in memory"
    ;; ret rf.

  Definition try_write {E}
             `{stateE state -< E}
             (* `{exceptE disabled -< E} *)
             (* `{exceptE error -< E} *)
             (tid : thread_id_t) (iid : instruction_id_t) (w : mem_write)
    : itree E unit :=
    s <- get
    ;; put (s <| mem := (tid, iid, w)::s.(mem) |>).

  Definition handle_storageE {E}
             `{stateE state -< E}
             `{exceptE disabled -< E}
             `{exceptE error -< E}
             (iid : instruction_id_t) (tid : thread_id_t)
    : storageE ~> itree E :=
    fun _ e =>
      match e with
      | StEReadInstruction pc => try_read_instruction pc
      | StERead read uslcs => try_read read uslcs
      | StEWrite write => try_write tid iid write
      end.
End Make.
