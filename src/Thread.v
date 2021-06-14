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

Require Import Types Utils.
Require Import  Decision.

Module Make (Arc : ArcSig).
  Variant threadE : Type -> Type :=
  | ThEFetchAndDecodeOrRestart : threadE (list instruction_id_t * Arc.InsSem.ast)
  | ThEFinishIns : threadE unit
  | ThERegAccess : forall A, Arc.InsSem.regE A -> threadE A
  (** Load events *)
  | ThEInitMemLoadOps : mem_slc -> threadE (list mem_read_id_t)
  (* [ThESatMemLoadOpForwarding] returns a bool that indicates if the read
     was fully satisfied, and a list of iids that should be restarted. *)
  | ThESatMemLoadOpForwarding : mem_read_id_t -> threadE (bool * list instruction_id_t)
  (* [ThESatMemLoadOpStorage] returns a list of iids that should be restarted. *)
  | ThESatMemLoadOpStorage : mem_read_id_t -> threadE (list instruction_id_t)
  | ThECompleteLoadOps : threadE mem_slc_val
  (** Store events *)
  | ThEInitMemStoreOpFps : mem_slc -> threadE unit
  | ThEInstaMemStoreOpVals : mem_slc_val -> threadE unit
  | ThECommitStoreInstruction : threadE (list mem_write_id_t)
  (* [ThEPropagateStoreOp] returns a list of iids that should be restarted. *)
  | ThEPropagateStoreOp : mem_write_id_t -> threadE (list instruction_id_t)
  | ThECompleteStoreOps : threadE unit.

  Definition lift_regE {E} `{threadE -< E}
    : Arc.InsSem.regE ~> itree E :=
    fun _ e => trigger (ThERegAccess _ e).

  Definition denote_restarts {E} `{schedulerE instruction_id_t -< E}
    : ktree E (list instruction_id_t) unit :=
    fun iids =>
      'tt <- trigger (Kill iids)
      ;; ITree.iter (fun respawn =>
                       match respawn with
                       | [] => ret (inr tt)
                       | iid::respawn =>
                         'tt <- trigger (Spawn iid)
                         ;; ret (inl respawn)
                       end) iids.

  Definition lift_mem_read {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
             (slc : mem_slc)
    : itree E mem_slc_val :=
    rids <- trigger (ThEInitMemLoadOps slc)
    ;; ITree.iter (fun rids => (* Reads that aren't fully satisfied yet. *)
                     match rids with
                     | [] =>
                       v <- trigger ThECompleteLoadOps
                       ;; ret (inr v)
                     | _ =>
                       rid <- choose rids
                       ;; read <- choose [trigger (ThESatMemLoadOpForwarding rid);
                                        (restarts <- trigger (ThESatMemLoadOpStorage rid)
                                         ;; ret (true, restarts))]
                       ;; is_sat <- exclusive_block
                                     ('(is_sat, restarts) <- read
                                      ;; 'tt <- denote_restarts restarts
                                      ;; ret is_sat)
                       ;; ret (inl (if (is_sat : bool) then
                                      List.remove Nat.eq_dec rid rids
                                    else rids))
                     end) rids.

  Definition lift_mem_write_fp {E} `{threadE -< E} `{nondetFinE -< E}
             (slc : mem_slc)
    : itree E unit :=
    trigger (ThEInitMemStoreOpFps slc).

  Definition lift_mem_write_val {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
             (val : mem_slc_val)
    : itree E unit :=
    'tt <- trigger (ThEInstaMemStoreOpVals val)
    ;; wids <- trigger ThECommitStoreInstruction
    ;; ITree.iter (fun wids => (* wids that haven't been propagated yet *)
                     match wids with
                     | [] =>
                       'tt <- trigger ThECompleteStoreOps
                       ;; ret (inr tt)
                     | _ =>
                       wid <- choose wids
                       ;; 'tt <- exclusive_block
                                  (restarts <- trigger (ThEPropagateStoreOp wid)
                                   ;; denote_restarts restarts)
                       ;; ret (inl (List.remove Nat.eq_dec wid wids))
                     end) wids.

  Definition lift_memE {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
    : Arc.InsSem.memE ~> itree E :=
    fun _ e =>
      match e with
      | Arc.InsSem.MemERead slc => lift_mem_read slc
      | Arc.InsSem.MemEWriteFP slc => lift_mem_write_fp slc
      | Arc.InsSem.MemEWriteVal val => lift_mem_write_val val
      end.

  Definition lift_ins_sem {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
    : itree Arc.InsSem.E ~> itree E :=
    fun _ it =>
      let h := case_ lift_regE lift_memE in
      interp h it.

  Definition spawn_instruction {E}
             `{wrapE threadE instruction_id_t -< E}
             `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
    : ktree E instruction_id_t (Types.result unit unit) :=
    fun iid =>
      let it : itree (threadE +' nondetFinE +' schedulerE instruction_id_t)
                     (Types.result unit unit) :=
          '(next_iids, ast) <- trigger ThEFetchAndDecodeOrRestart
          ;; 'tt <- ITree.iter (fun next_iids =>
                                 match next_iids with
                                 | [] => ret (inr tt)
                                 | niid::next_ins => trigger (Spawn niid)
                                                   ;; ret (inl next_iids)
                                 end) next_iids
          ;; 'tt <- resum_it _ (lift_ins_sem _ (Arc.InsSem.denote ast))
          ;; 'tt <- trigger ThEFinishIns
          ;; ret (Accept tt) in
      (* Finnaly, wrap the threadE events with the iid *)
      resum_it _ (wrap_event_in_it threadE iid _ it).

  Definition denote {E}
             `{wrapE threadE instruction_id_t -< E} `{nondetFinE -< E}
    : ktree E instruction_id_t (Types.result unit unit) :=
    fun iid =>
      resum_it _ (scheduler Nat.eqb spawn_instruction
                            (fun r1 r2 => match r1, r2 with
                                       | Accept tt, Accept tt => Accept tt
                                       | _, _ => Reject tt
                                       end)
                            (Accept tt)
                            [(iid, spawn_instruction iid)]
                            None).

(*******************************************************************************)
(** State **********************************************************************)
(*******************************************************************************)

  Record reg_read_state :=
    mk_reg_read_state { rrs_slc : Arc.InsSem.reg_slc;
                        rrs_feeding_addr : bool;
                        rrs_reads_from : list (instruction_id_t * nat);
                                             (* the [nat] is an index into [ins_reg_writes.rws_slc]
                                                of the instruction pointed by the [instruction_id_t]. *)
                        rrs_val : option Arc.InsSem.reg_val }.

  Record reg_write_state :=
    mk_reg_write_state { rws_slc : Arc.InsSem.reg_slc;
                         rws_val : option Arc.InsSem.reg_val;
                         (* [rws_reg_data_flow] is a concatination of all the
                            [rrs_reads_from] of the instruction, when the
                            reg-write was performed. We assume that there is a
                            data-flow from those to this reg-write, and therefore
                            a dependency between the feeding instructions and
                            any instruction that reads from this
                            register-write. *)
                         rws_reg_data_flow : list (instruction_id_t * nat);
                         (* [rws_mem_data_flow] indicates if the instruction has
                            performed a memory read before the reg-write. If so,
                            we assume that there is a data-flow from the memory
                            to this reg-write. *)
                         rws_mem_data_flow : bool }.


  Record mem_reads_state :=
    mk_mem_reads_state { rs_footprint : mem_slc;
                         rs_reads : list Arc.mem_read;
                         rs_unsat_slcs : list (list mem_slc);
                         rs_reads_from : list Arc.mem_reads_from }.

  Instance eta_mem_reads_state : Settable _ :=
    settable! mk_mem_reads_state <rs_footprint; rs_reads; rs_unsat_slcs; rs_reads_from>.

  Record mem_writes_state :=
    mk_mem_writes_state { ws_footprint : mem_slc;
                          ws_writes : list Arc.mem_write;
                          ws_has_propagated : list bool }.

  Instance eta_mem_writes_state : Settable _ :=
    settable! mk_mem_writes_state <ws_footprint; ws_writes; ws_has_propagated>.

  Record decoded_instruction_state :=
    mk_decoded_instruction_state {
        ins_ast : Arc.InsSem.ast;
        (* statically analysed data about the instruction*)
        ins_kind : Arc.instruction_kind;

        ins_reg_reads : list reg_read_state;
        ins_reg_writes : list reg_write_state;

        ins_mem_reads : option mem_reads_state;
        ins_mem_writes : option mem_writes_state;

        ins_finished : bool }.

  Instance eta_decoded_instruction_state : Settable _ :=
    settable! mk_decoded_instruction_state <ins_ast; ins_kind; ins_reg_reads; ins_reg_writes; ins_mem_reads; ins_mem_writes; ins_finished>.

  Definition initial_decoded_instruction_state
             (ast : Arc.InsSem.ast)
    : decoded_instruction_state :=
    let '(regs_in, regs_out) := Arc.InsSem.regs_from_ast ast in
    {| ins_ast := ast;
       ins_kind := (Arc.instruction_kind_from_ast ast);
       ins_reg_reads := List.map (fun '(slc, addr) => mk_reg_read_state slc addr [] None) regs_in;
       ins_reg_writes := List.map (fun slc => mk_reg_write_state slc None [] false) regs_out;
       ins_mem_reads := None;
       ins_mem_writes := None;
       ins_finished := false |}.

  Definition instruction_state : Type := instruction_id_t *
                                         mem_loc *
                                         option decoded_instruction_state.

  Record state :=
    mk_state { next_iid : instruction_id_t;
               instruction_tree : tree instruction_state }.

  Instance eta_state : Settable _ :=
    settable! mk_state <next_iid; instruction_tree>.

  Definition initial_state (iid : instruction_id_t) (loc : mem_loc)
    : state :=
    {| next_iid := iid + 1;
       instruction_tree := Tree (iid, loc, None) [] |}.

  Definition get_instruction_state {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (list instruction_state * instruction_state * list (tree instruction_state)) :=
    let fix helper prefix t :=
        let '(Tree ((iid', _, _) as i) subts) := t in
        if Nat.eqb iid' iid then Some (prefix, i, subts)
        else
          match List.find (fun x => match x with None => false | _ => true end)
                          (List.map (helper (i::prefix)) subts) with
          | Some x => x
          | None => None
          end
    in
    try_unwrap_option (helper [] s.(instruction_tree)) "get_instruction_state: Can't find iid".

  Definition get_dec_instruction_state {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (list instruction_state * decoded_instruction_state * list (tree instruction_state)) :=
    '(prefix, (_, _, ins), subts) <- get_instruction_state iid s
    ;; dins <- try_unwrap_option ins "get_dec_instruction_state: instruction was not decoded yet"
    ;; ret (prefix, dins, subts).

  Definition update_dec_instruction_state_and_subts
             (iid : instruction_id_t) (dins : decoded_instruction_state)
             (subts : list (tree instruction_state)) (s : state)
    : state :=
    let fix helper t :=
        let '(Tree ((iid', loc, _) as i) subts') := t in
        if Nat.eqb iid' iid then Tree (iid, loc, Some dins) subts
        else Tree i (List.map helper subts')
    in
    s <| instruction_tree := helper s.(instruction_tree) |>.

  Definition update_dec_instruction_state
             (iid : instruction_id_t) (dins : decoded_instruction_state)
             (s : state)
    : state :=
    let fix helper t :=
        let '(Tree ((iid', loc, _) as i) subts) := t in
        if Nat.eqb iid' iid then Tree (iid, loc, Some dins) subts
        else Tree i (List.map helper subts)
    in
    s <| instruction_tree := helper s.(instruction_tree) |>.

  Definition try_fetch_and_decode_or_restart {E} `{Arc.storageE -< E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * (list instruction_id_t * Arc.InsSem.ast)) :=
    '(_, (_, loc, ins), _) <- get_instruction_state iid s
    ;; match ins with
       | None =>
         '(slc, rf) <- trigger (Arc.StEReadInstruction loc)
         ;; val <- try_unwrap_option (mem_slc_val_of_reads_from slc rf)
                                    "try_fetch_and_decode_or_restart: some bytes are missing from memory read of instruction."
         ;; let ast := Arc.InsSem.decode (nat_of_mem_slc_val val) in
            let ins := initial_decoded_instruction_state ast in
            let next_pcs := Arc.InsSem.next_pc (Arc.pc_of_mem_loc loc) ast in
            let next_pcs := List.map Arc.mem_loc_of_pc next_pcs in
            let iids := List.seq s.(next_iid) (List.length next_pcs) in
            let subts := List.map (fun '(iid, pc) => Tree (iid, pc, None) [])
                                  (List.combine iids next_pcs) in
            let s := s <| next_iid := s.(next_iid) + (List.length next_pcs) |> in
            let s := update_dec_instruction_state_and_subts iid ins subts s in
            ret (s, (iids, ast))
       | Some ins =>
         (* Nothing to do, the instruction-state has already been restarted. *)
         ret (s, ([], ins.(ins_ast)))
       end.

  Definition try_finish_instruction {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    (* FIXME: check finish condition *)
    ret (s, tt).

  Definition try_read_reg_slc {E}
             (rslc : Arc.InsSem.reg_slc) (iid : instruction_id_t) (s : state)
    : itree E (state * Arc.InsSem.reg_val) :=
    ITree.spin.

  Definition try_write_reg_slc {E} `{exceptE error -< E}
             (rslc : Arc.InsSem.reg_slc) (val : Arc.InsSem.reg_val)
             (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    '(_, ins, _) <- get_dec_instruction_state iid s
    ;; let reg_writes :=
           List.map
             (fun rws =>
                if Arc.InsSem.reg_slc_eqb rws.(rws_slc) rslc then
                  let rdf := List.concat (List.map rrs_reads_from ins.(ins_reg_reads)) in
                  let mdf := match ins.(ins_mem_reads) with Some _ => true | _ => false end in
                  mk_reg_write_state rslc (Some val) rdf mdf
                else rws)
             ins.(ins_reg_writes) in
       let ins := ins <| ins_reg_writes := reg_writes |> in
       let s := update_dec_instruction_state iid ins s in
       ret (s, tt).

  Definition handle_reg_access {E} `{exceptE error -< E}
             (iid : instruction_id_t)
    : Arc.InsSem.regE ~> stateT state (itree E) :=
    fun _ e s =>
      match e with
      | Arc.InsSem.RegERead rslc => try_read_reg_slc rslc iid s
      | Arc.InsSem.RegEWrite rslc rval => try_write_reg_slc rslc rval iid s
      end.

  Definition try_init_mem_load_ops {E} `{exceptE error -< E}
             (slc : mem_slc) (iid : instruction_id_t) (s : state)
    : itree E (state * list mem_read_id_t) :=
    '(_, ins, _) <- get_dec_instruction_state iid s
    ;; let sub_slcs := Arc.split_load_mem_slc ins.(ins_kind) slc in
       let kind := Arc.mem_read_kind_of_ins_kind ins.(ins_kind) in
       let rids := List.seq 0 (List.length sub_slcs) in
       let reads := List.map
                      (fun '(rid, slc) => {| Arc.read_id := rid;
                                          Arc.read_footprint := slc;
                                          Arc.read_kind := kind |})
                      (List.combine rids sub_slcs) in
       let rs := {| rs_footprint := slc;
                    rs_reads := reads;
                    rs_unsat_slcs := List.map (fun r => [r.(Arc.read_footprint)]) reads;
                    rs_reads_from := List.map (fun _ => nil) reads |} in
       let ins := ins <| ins_mem_reads := Some rs |> in
       let s := update_dec_instruction_state iid ins s in
       ret (s, rids).


  Definition try_sat_mem_load_op_forwarding {E} `{exceptE error -< E} `{exceptE disabled -< E}
             (rid : mem_read_id_t) (iid : instruction_id_t) (s : state)
    : itree E (state * (bool * list instruction_id_t)) :=
    (* FIXME: *)
    ITree.spin.

  Definition try_sat_mem_load_op_from_storage {E}
             `{exceptE error -< E} `{exceptE disabled -< E}
             `{Arc.storageE -< E}
             (rid : mem_read_id_t) (iid : instruction_id_t) (s : state)
    : itree E (state * list instruction_id_t) :=
    '(_, ins, subts) <- get_dec_instruction_state iid s
    ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                    "try_sat_mem_load_op_from_storage: no mem reads."
    ;; unsat_slcs <- try_unwrap_option (List.nth_error rs.(rs_unsat_slcs) rid)
                                      "try_sat_mem_load_op_from_storage: missing rid."
    (* ;; guard (isTrue (unsat_slcs <> [])) *)
    ;; rr <- try_unwrap_option (List.nth_error rs.(rs_reads) rid)
                              "try_sat_mem_load_op_from_storage: missing rid"
    ;; rf_forward <- try_unwrap_option (List.nth_error rs.(rs_reads_from) rid)
                                      "try_sat_mem_load_op_from_storage: missing rid."
    ;; rf_storage <- trigger (Arc.StERead rr unsat_slcs)
    ;; let rs := rs <| rs_unsat_slcs := list_replace_nth rid [] rs.(rs_unsat_slcs) |>
                    <| rs_reads_from := list_replace_nth rid (rf_forward ++ rf_storage) rs.(rs_reads_from) |> in
       let ins := ins <| ins_mem_reads := Some rs |> in
       (* FIXME: compute iids that need to be restarted *)
       let restarts := [] in
       (* FIXME: let subts := restart_instructions restarts subts in *)
       let s := update_dec_instruction_state_and_subts iid ins subts s in
       ret (s, restarts).

  Definition try_complete_load_ops {E} `{exceptE error -< E} `{exceptE disabled -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * mem_slc_val) :=
    '(_, ins, _) <- get_dec_instruction_state iid s
    ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                    "try_complete_load_ops: no mem reads."
    (* ;; guard (isTrue (Forall (fun u => u = []) rs.(rs_unsat_slcs))) *)
    ;; val <- try_unwrap_option
               (mem_slc_val_of_reads_from
                  rs.(rs_footprint)
                       (List.concat rs.(rs_reads_from)))
               "try_complete_load_ops: some bytes are missing from memory read."
    ;; ret (s, val).

  Definition try_init_mem_store_op_fps {E} `{exceptE error -< E} `{exceptE disabled -< E}
             (slc : mem_slc) (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    '(_, ins, _) <- get_dec_instruction_state iid s
    ;; let ws := {| ws_footprint := slc;
                    ws_writes := [];
                    ws_has_propagated := [] |} in
       let ins := ins <| ins_mem_writes := Some ws |> in
       let s := update_dec_instruction_state iid ins s in
       ret (s, tt).

  Definition try_insta_mem_store_op_vals {E} `{exceptE error -< E} `{exceptE disabled -< E}
             (val : mem_slc_val) (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    '(_, ins, _) <- get_dec_instruction_state iid s
    ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                    "try_insta_mem_store_op_vals: no mem writes"
    ;; let sub_slcs := Arc.split_store_mem_slc_val ins.(ins_kind) ws.(ws_footprint) val in
       let kind := Arc.mem_write_kind_of_ins_kind ins.(ins_kind) in
       let wids := List.seq 0 (List.length sub_slcs) in
       let writes := List.map
                      (fun '(wid, (slc, val)) => {| Arc.write_id := wid;
                                                 Arc.write_footprint := slc;
                                                 Arc.write_val := val;
                                                 Arc.write_kind := kind |})
                      (List.combine wids sub_slcs) in
       let ws := ws <| ws_writes := writes |>
                    <| ws_has_propagated := List.map (fun _ => false) writes |>in
       let ins := ins <| ins_mem_writes := Some ws |> in
       let s := update_dec_instruction_state iid ins s in
       ret (s, tt).

  Definition try_commit_store_instruction {E} `{exceptE error -< E} `{exceptE disabled -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * list mem_write_id_t) :=
    '(_, ins, _) <- get_dec_instruction_state iid s
    ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                    "try_commit_store_instruction: no mem writes"
    (* FIXME: check commit-store condition *)
    ;; let wids := List.map Arc.write_id ws.(ws_writes) in
    ret (s, wids).

  Definition try_propagate_store_op {E}
             `{exceptE error -< E} `{exceptE disabled -< E}
             `{Arc.storageE -< E}
             (wid : mem_write_id_t) (iid : instruction_id_t) (s : state)
    : itree E (state * list instruction_id_t) :=
    '(_, ins, subts) <- get_dec_instruction_state iid s
    ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                    "try_propagate_store_op: no mem writes"
    (* ;; guard (isTrue (List.nth_error ws.(ws_has_propagated) wid = Some false)) *)
    ;; w <- try_unwrap_option (List.nth_error ws.(ws_writes) wid)
                              "try_propagate_store_op: missing wid"
    (* FIXME: check mem-write-propagation condition *)
    ;; 'tt <- trigger (Arc.StEWrite w)
    ;; let ws := ws <| ws_has_propagated := list_replace_nth wid true ws.(ws_has_propagated) |> in
       let ins := ins <| ins_mem_writes := Some ws |> in
       (* FIXME: compute iids that need to be restarted *)
       let restarts := [] in
       (* FIXME: let subts := restart_instructions restarts subts in *)
       let s := update_dec_instruction_state_and_subts iid ins subts s in
       ret (s, restarts).

  Definition try_complete_store_ops {E} `{exceptE error -< E} `{exceptE disabled -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    (* FIXME: is there anything we need to check here? *)
    ret (s, tt).

  Definition handle_threadE {E}
             `{exceptE error -< E} `{exceptE disabled -< E}
             `{Arc.storageE -< E}
             (iid : instruction_id_t)
    : threadE ~> stateT state (itree E) :=
    fun _ e s =>
      match e with
      | ThEFetchAndDecodeOrRestart => try_fetch_and_decode_or_restart iid s
      | ThEFinishIns => try_finish_instruction iid s
      | ThERegAccess _ e => handle_reg_access iid _ e s
      (* Load events *)
      | ThEInitMemLoadOps slc => try_init_mem_load_ops slc iid s
      | ThESatMemLoadOpForwarding rid => try_sat_mem_load_op_forwarding rid iid s
      | ThESatMemLoadOpStorage rid => try_sat_mem_load_op_from_storage rid iid s
      | ThECompleteLoadOps => try_complete_load_ops iid s
      (* Store events *)
      | ThEInitMemStoreOpFps slc => try_init_mem_store_op_fps slc iid s
      | ThEInstaMemStoreOpVals val => try_insta_mem_store_op_vals val iid s
      | ThECommitStoreInstruction => try_commit_store_instruction iid s
      | ThEPropagateStoreOp wid => try_propagate_store_op wid iid s
      | ThECompleteStoreOps => try_complete_store_ops iid s
      end.
End Make.
