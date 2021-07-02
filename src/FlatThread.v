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

From bbv Require Import Word.
Import Word.Notations.

Require Import Types Utils.
Require Import  Decision.

Module Make (Arc : ArcSig) : ThreadSig Arc.
  Export Arc.

  Variant _E : Type -> Type :=
  | ThEFetchAndDecodeOrRestart : _E (list instruction_id_t * ast)
  | ThEFinishIns : _E unit
  | ThERegAccess : forall A, regE A -> _E A
  (** Load events *)
  | ThEInitMemLoadOps : mem_slc -> _E (list mem_read_id_t)
  (* [ThESatMemLoadOpForwarding] returns a bool that indicates if the read
     was fully satisfied, and a list of iids that should be restarted. *)
  | ThESatMemLoadOpForwarding : mem_read_id_t -> _E (bool * list instruction_id_t)
  (* [ThESatMemLoadOpStorage] returns a list of iids that should be restarted. *)
  | ThESatMemLoadOpStorage : mem_read_id_t -> _E (list instruction_id_t)
  | ThECompleteLoadOps : _E mem_slc_val
  (** Store events *)
  | ThEInitMemStoreOpFps : mem_slc -> _E unit
  | ThEInstaMemStoreOpVals : mem_slc_val -> _E unit
  | ThECommitStoreInstruction : _E (list mem_write_id_t)
  (* [ThEPropagateStoreOp] returns a list of iids that should be restarted. *)
  | ThEPropagateStoreOp : mem_write_id_t -> _E (list instruction_id_t)
  | ThECompleteStoreOps : _E unit.
  (* Workaround: parameter can't be instantiated by an inductive type *)
  Definition E := _E.

  Instance showable_E : forall A, Showable (E A) :=
    { show := fun e =>
                match e with
                | ThEFetchAndDecodeOrRestart => "ThEFetchAndDecodeOrRestart"%string
                | ThEFinishIns => "ThEFinishIns"%string
                | ThERegAccess _ regE => "ThERegAccess"%string
                (** Load events *)
                | ThEInitMemLoadOps mem_slc => "ThEInitMemLoadOps"%string
                | ThESatMemLoadOpForwarding mem_read_id_t => "ThESatMemLoadOpForwarding"%string
                | ThESatMemLoadOpStorage mem_read_id_t => "ThESatMemLoadOpStorage"%string
                | ThECompleteLoadOps => "ThECompleteLoadOps"%string
                (** Store events *)
                | ThEInitMemStoreOpFps mem_slc => "ThEInitMemStoreOpFps"%string
                | ThEInstaMemStoreOpVals mem_slc_val => "ThEInstaMemStoreOpVals"%string
                | ThECommitStoreInstruction => "ThECommitStoreInstruction"%string
                | ThEPropagateStoreOp mem_write_id_t => "ThEPropagateStoreOp"%string
                | ThECompleteStoreOps => "ThECompleteStoreOps"%string
                end
    }.

  Section Denote.
    Definition lift_regE {F} `{E -< F}
    : regE ~> itree F :=
      fun _ e => trigger (ThERegAccess _ e).

    Definition denote_restarts {F} `{schedulerE instruction_id_t -< F}
      : ktree F (list instruction_id_t) unit :=
      fun iids =>
        'tt <- trigger (Kill iids)
        ;; ITree.iter (fun respawn =>
                         match respawn with
                         | [] => ret (inr tt)
                         | iid::respawn =>
                           'tt <- trigger (Spawn iid)
                           ;; ret (inl respawn)
                         end) iids.

    Definition lift_mem_read {F}
               `{E -< F} `{nondetFinE -< F}
               `{schedulerE instruction_id_t -< F}
               (slc : mem_slc)
      : itree F mem_slc_val :=
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

    Definition lift_mem_write_fp {F} `{E -< F} `{nondetFinE -< F}
               (slc : mem_slc)
      : itree F unit :=
      trigger (ThEInitMemStoreOpFps slc).

    Definition lift_mem_write_val {F}
               `{E -< F} `{nondetFinE -< F}
               `{schedulerE instruction_id_t -< F}
               (val : mem_slc_val)
      : itree F unit :=
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

    Definition lift_memE {F}
               `{E -< F} `{nondetFinE -< F}
               `{schedulerE instruction_id_t -< F}
      : memE ~> itree F :=
      fun _ e =>
        match e with
        | MemERead slc => lift_mem_read slc
        | MemEWriteFP slc => lift_mem_write_fp slc
        | MemEWriteVal val => lift_mem_write_val val
        end.

    Definition lift_ins_sem {F}
               `{E -< F} `{nondetFinE -< F}
               `{schedulerE instruction_id_t -< F}
      : itree insSemE ~> itree F :=
      fun _ it =>
        let h := case_ lift_regE lift_memE in
        resum_it _ (interp h it).

    Definition spawn_instruction {F}
               `{wrapE E instruction_id_t -< F}
               `{nondetFinE -< F}
               `{schedulerE instruction_id_t -< F}
               `{debugE -< F}
      : ktree F instruction_id_t (Types.result unit unit) :=
      fun iid =>
        let it : itree (E +' nondetFinE +' schedulerE instruction_id_t +' debugE)
                       (Types.result unit unit) :=
            'tt <- trigger (Debug ("spawn_instruction: iid '" ++ show iid ++ "'"))
            ;; '(next_iids, ast) <- trigger ThEFetchAndDecodeOrRestart
            ;; 'tt <- ITree.iter (fun next_iids =>
                                   match next_iids with
                                   | [] => ret (inr tt)
                                   | niid::next_iids => trigger (Spawn niid)
                                                     ;; ret (inl next_iids)
                                   end) next_iids
            ;; 'tt <- resum_it _ (lift_ins_sem _ (denote ast))
            ;; 'tt <- trigger ThEFinishIns
            ;; ret (Accept tt) in
        (* Finnaly, wrap the E events with the iid *)
        resum_it _ (wrap_event_in_it E iid _ it).

    Definition denote {F}
               `{wrapE E instruction_id_t -< F}
               `{nondetFinE -< F}
               `{debugE -< F}
      : ktree F instruction_id_t (Types.result unit unit) :=
      fun iid =>
        resum_it _ (scheduler Nat.eqb spawn_instruction
                              (fun r1 r2 => match r1, r2 with
                                         | Accept tt, Accept tt => Accept tt
                                         | _, _ => Reject tt
                                         end)
                              (Accept tt)
                              [(iid, spawn_instruction iid)]
                              None).
  End Denote.

  Section State.
    Record reg_read_state :=
      mk_reg_read_state { rrs_slc : reg_slc;
                          rrs_feeding_addr : bool;
                          rrs_reads_from : list (instruction_id_t * nat * reg_slc_val);
                          (* the [nat] is an index into [ins_reg_writes.rws_slc]
                                                of the instruction pointed by the [instruction_id_t]. *)
                          rrs_val : option (reg_val rrs_slc.(rs_size)) }.

    Record reg_write_state :=
      mk_reg_write_state { rws_slc : reg_slc;
                           rws_val : option (reg_val rws_slc.(rs_size));
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
                           rs_reads : list mem_read;
                           rs_unsat_slcs : list (list mem_slc);
                           rs_reads_from : list mem_reads_from }.

    Instance eta_mem_reads_state : Settable _ :=
      settable! mk_mem_reads_state <rs_footprint; rs_reads; rs_unsat_slcs; rs_reads_from>.

    Record mem_writes_state :=
      mk_mem_writes_state { ws_footprint : mem_slc;
                            ws_writes : list mem_write;
                            ws_has_propagated : list bool }.

    Instance eta_mem_writes_state : Settable _ :=
      settable! mk_mem_writes_state <ws_footprint; ws_writes; ws_has_propagated>.

    Record decoded_instruction_state :=
      mk_decoded_instruction_state {
          ins_ast : ast;

          ins_reg_reads : list reg_read_state;
          ins_reg_writes : list reg_write_state;

          ins_mem_reads : option mem_reads_state;
          ins_mem_writes : option mem_writes_state;

          ins_finished : bool }.

    Instance eta_decoded_instruction_state : Settable _ :=
      settable! mk_decoded_instruction_state <ins_ast; ins_reg_reads; ins_reg_writes; ins_mem_reads; ins_mem_writes; ins_finished>.

    Definition initial_decoded_instruction_state
               (ast : ast)
      : decoded_instruction_state :=
      let info := info_of_ast ast in
      {| ins_ast := ast;
         ins_reg_reads := List.map (fun '(slc, addr) => mk_reg_read_state slc addr [] None)
                                   info.(input_regs);
         ins_reg_writes := List.map (fun slc => mk_reg_write_state slc None [] false)
                                    info.(output_regs);
         ins_mem_reads := None;
         ins_mem_writes := None;
         ins_finished := false |}.

    Definition instruction_state : Type := instruction_id_t *
                                           mem_loc *
                                           option decoded_instruction_state.

    Record _state :=
      mk_state { next_iid : instruction_id_t;
                 instruction_tree : tree instruction_state }.
    (* Workaround: parameter can't be instantiated by an inductive type *)
    Definition state := _state.

    Instance eta_state : Settable _ :=
      settable! mk_state <next_iid; instruction_tree>.

    (* Instance showable_state : Showable state := *)
    (*   { show := *)
    (*       fun s => *)
    (*         let inss :=  *)
    (*         ""%string *)
    (*   }. *)

    Definition initial_state (iid : instruction_id_t) (loc : mem_loc)
      : state :=
      {| next_iid := iid + 1;
         instruction_tree := Tree (iid, loc, None) [] |}.

    Section RegisterRead.
      Local Instance slice_id_rsv : Slice (instruction_id_t * nat * reg_slc_val) :=
        { start := fun '(_, _, s) => Utils.start s;
          size := fun '(_, _, s) => Utils.size s;
          sub_slice := fun '(id, s) start size =>
                         match sub_slice s start size with
                         | Some s' => Some (id, s')
                         | None => None
                         end }.

      Fixpoint read_reg_slcs
               (rslcs : list reg_slc)
               (pref : list instruction_state)
               (rf : list (instruction_id_t * nat * reg_slc_val))
        : option (list (instruction_id_t * nat * reg_slc_val)) :=
        match pref with
        | (iid, _, Some ins)::pref =>
          match Utils.reads_from_slcs
                  (List.map (fun '(i, w) => ((iid, i), {| rsv_slc := w.(rws_slc);
                                                       rsv_val := w.(rws_val) |}))
                            (List.combine (List.seq 0 (List.length ins.(ins_reg_writes)))
                                          ins.(ins_reg_writes)))
                  rslcs rf with
          | Some (rf, nil) => Some rf
          | Some (rf, rslcs) => read_reg_slcs rslcs pref rf
          | None => None
          end
        | (iid, _, None)::_ => None
        | nil =>
          (* FIXME: read initial value; for now read 0 *)
          Some (List.fold_left (fun rf rslc =>
                                  (0, 0, {| rsv_slc := rslc;
                                            rsv_val :=
                                              Some (wzero rslc.(rs_size)) |})::rf)
                               rslcs
                               rf)
        end.

      Program Definition reg_val_of_reads_from (slc : reg_slc)
                 (rf : list ((instruction_id_t * nat) * reg_slc_val))
        : reg_val slc.(rs_size) :=
        List.fold_left
          (fun w '(_, rsv) =>
             match rsv.(rsv_val) with
             | Some val =>
               if decide (rsv.(rsv_slc).(rs_size)
                          <= slc.(rs_size) /\
                          slc.(rs_first_bit)
                          <= rsv.(rsv_slc).(rs_first_bit)) then
                 let w' := zext val (slc.(rs_size) -
                                     rsv.(rsv_slc).(rs_size)) in
                 let w' := (w' ^<< (rsv.(rsv_slc).(rs_first_bit) -
                                    slc.(rs_first_bit)))%word in
                 wor w w'
               else
                 (* FIXME: this shouldn't be reachable *)
                 w
             | None =>
               (* FIXME: this shouldn't be reachable *)
               w
             end)
          rf (wzero slc.(rs_size)).
      Obligation 1.
      rewrite Nat.add_comm. apply Nat.sub_add. auto.
      Qed.
    End RegisterRead.

    Definition get_instruction_state {F} `{exceptE error -< F}
               (iid : instruction_id_t) (s : state)
      : itree F (list instruction_state * instruction_state * list (tree instruction_state)) :=
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
      try_unwrap_option (helper [] s.(instruction_tree))
                        ("get_instruction_state: Can't find iid '" ++ show iid ++ "'").

    Definition get_dec_instruction_state {F} `{exceptE error -< F}
               (iid : instruction_id_t) (s : state)
      : itree F (list instruction_state * decoded_instruction_state * list (tree instruction_state)) :=
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

    Section Handle_instruction_instance.
      Context {F : Type -> Type}.
      Context `{storageE -< F}.
      Context `{stateE state -< F}.
      Context `{exceptE disabled -< F}.
      Context `{exceptE error -< F}.
      Context `{debugE -< F}.

      Variable iid : instruction_id_t.

      Definition try_fetch_and_decode_or_restart
        : itree F (list instruction_id_t * ast) :=
        s <- get
        ;; '(_, (_, loc, ins), _) <- get_instruction_state iid s
        ;; match ins with
           | None =>
             '(slc, rf) <- trigger (StEReadInstruction loc)
             ;; val <- try_unwrap_option (mem_slc_val_of_reads_from slc rf)
                                        "try_fetch_and_decode_or_restart: some bytes are missing from memory read of instruction."
             ;; ast <- try_unwrap_option (decode val)
                                        "try_fetch_and_decode_or_restart: decoding of instruction failed"
             ;; let ins := initial_decoded_instruction_state ast in
                let next_pcs := next_pc loc ast in
                let iids := List.seq s.(next_iid) (List.length next_pcs) in
                let subts := List.map (fun '(iid, pc) => Tree (iid, pc, None) [])
                                      (List.combine iids next_pcs) in
                let s := s <| next_iid := s.(next_iid) + (List.length next_pcs) |> in
                let s := update_dec_instruction_state_and_subts iid ins subts s in
                'tt <- put s
                ;; ret (iids, ast)
           | Some ins =>
             (* Nothing to do, the instruction-state has already been restarted. *)
             ret ([], ins.(ins_ast))
           end.

      Definition try_finish_instruction : itree F unit :=
        (* FIXME: check finish condition *)
        let iid := iid in
        ret tt.

      Definition try_read_reg_slc (rslc : reg_slc)
        : itree F (reg_val rslc.(rs_size)) :=
        s <- get
        ;; '(pref, ins, _) <- get_dec_instruction_state iid s
        ;; match read_reg_slcs [rslc] pref [] with
           | Some rf =>
             let val := reg_val_of_reads_from rslc rf in
             let reg_reads :=
                 List.map
                   (fun rrs =>
                      if decide (rrs.(rrs_slc) = rslc) then
                        mk_reg_read_state rslc rrs.(rrs_feeding_addr) rf (Some val)
                      else rrs)
                   ins.(ins_reg_reads) in
             let ins := ins <| ins_reg_reads := reg_reads |> in
             let s := update_dec_instruction_state iid ins s in
             'tt <- put s
             ;; ret val
           | None => throw (Disabled tt)
           end.

      Definition try_write_reg_slc (rslc : reg_slc)
                 (val : reg_val rslc.(rs_size))
        : itree F unit :=
        s <- get
        ;; '(_, ins, _) <- get_dec_instruction_state iid s
        ;; let reg_writes :=
               List.map
                 (fun rws =>
                    if decide (rws.(rws_slc) = rslc) then
                      let rdf := List.concat (List.map (fun rrs => List.map fst rrs.(rrs_reads_from))
                                                       ins.(ins_reg_reads)) in
                      let mdf := match ins.(ins_mem_reads) with Some _ => true | _ => false end in
                      mk_reg_write_state rslc (Some val) rdf mdf
                    else rws)
                 ins.(ins_reg_writes) in
           let ins := ins <| ins_reg_writes := reg_writes |> in
           let s := update_dec_instruction_state iid ins s in
           put s.

      Definition handle_reg_access : regE ~> itree F :=
        fun _ e =>
          match e with
          | RegERead rslc => try_read_reg_slc rslc
          | RegEWrite rslc rval => try_write_reg_slc rslc rval
          end.

      Definition try_init_mem_load_ops (slc : mem_slc)
        : itree F (list mem_read_id_t) :=
        s <- get
        ;; '(_, ins, _) <- get_dec_instruction_state iid s
        ;; let sub_slcs := split_load_mem_slc ins.(ins_ast) slc in
           let kind := mem_read_kind_of_ast ins.(ins_ast) in
           let rids := List.seq 0 (List.length sub_slcs) in
           let reads := List.map
                          (fun '(rid, slc) => {| read_id := rid;
                                              read_footprint := slc;
                                              read_kind := kind |})
                          (List.combine rids sub_slcs) in
           let rs := {| rs_footprint := slc;
                        rs_reads := reads;
                        rs_unsat_slcs := List.map (fun r => [r.(read_footprint)]) reads;
                        rs_reads_from := List.map (fun _ => nil) reads |} in
           let ins := ins <| ins_mem_reads := Some rs |> in
           let s := update_dec_instruction_state iid ins s in
           'tt <- put s
           ;; ret rids.


      Definition try_sat_mem_load_op_forwarding (rid : mem_read_id_t)
        : itree F (bool * list instruction_id_t) :=
        (* FIXME: *)
        let iid := iid in
        throw (Error "try_sat_mem_load_op_forwarding: not implemented").

      Definition try_sat_mem_load_op_from_storage (rid : mem_read_id_t)
        : itree F (list instruction_id_t) :=
        s <- get
        ;; '(_, ins, subts) <- get_dec_instruction_state iid s
        ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                        "try_sat_mem_load_op_from_storage: no mem reads."
        ;; unsat_slcs <- try_unwrap_option (List.nth_error rs.(rs_unsat_slcs) rid)
                                          "try_sat_mem_load_op_from_storage: missing rid."
        (* ;; guard (isTrue (unsat_slcs <> [])) *)
        ;; rr <- try_unwrap_option (List.nth_error rs.(rs_reads) rid)
                                  "try_sat_mem_load_op_from_storage: missing rid"
        ;; rf_forward <- try_unwrap_option (List.nth_error rs.(rs_reads_from) rid)
                                          "try_sat_mem_load_op_from_storage: missing rid."
        ;; rf_storage <- trigger (StERead rr unsat_slcs)
        ;; let rs := rs <| rs_unsat_slcs := list_replace_nth rid [] rs.(rs_unsat_slcs) |>
                                                                                       <| rs_reads_from := list_replace_nth rid (rf_forward ++ rf_storage) rs.(rs_reads_from) |> in
           let ins := ins <| ins_mem_reads := Some rs |> in
           (* FIXME: compute iids that need to be restarted *)
           let restarts := [] in
           (* FIXME: let subts := restart_instructions restarts subts in *)
           let s := update_dec_instruction_state_and_subts iid ins subts s in
           'tt <- put s
           ;; ret restarts.

      Definition try_complete_load_ops : itree F mem_slc_val :=
        s <- get
        ;; '(_, ins, _) <- get_dec_instruction_state iid s
        ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                        "try_complete_load_ops: no mem reads."
        (* ;; guard (isTrue (Forall (fun u => u = []) rs.(rs_unsat_slcs))) *)
        ;; val <- try_unwrap_option
                   (mem_slc_val_of_reads_from
                      rs.(rs_footprint)
                           (List.concat rs.(rs_reads_from)))
                   "try_complete_load_ops: some bytes are missing from memory read."
        ;; ret val.

      Definition try_init_mem_store_op_fps (slc : mem_slc) : itree F unit :=
        s <- get
        ;; '(_, ins, _) <- get_dec_instruction_state iid s
        ;; let ws := {| ws_footprint := slc;
                        ws_writes := [];
                        ws_has_propagated := [] |} in
           let ins := ins <| ins_mem_writes := Some ws |> in
           let s := update_dec_instruction_state iid ins s in
           put s.

      Definition try_insta_mem_store_op_vals (val : mem_slc_val) : itree F unit :=
        s <- get
        ;; '(_, ins, _) <- get_dec_instruction_state iid s
        ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                        "try_insta_mem_store_op_vals: no mem writes"
        ;; let sub_slcs := split_store_mem_slc_val ins.(ins_ast) ws.(ws_footprint) val in
           let kind := mem_write_kind_of_ast ins.(ins_ast) in
           let wids := List.seq 0 (List.length sub_slcs) in
           let writes := List.map
                           (fun '(wid, (slc, val)) => {| write_id := wid;
                                                      write_footprint := slc;
                                                      write_val := val;
                                                      write_kind := kind |})
                           (List.combine wids sub_slcs) in
           let ws := ws <| ws_writes := writes |>
                                               <| ws_has_propagated := List.map (fun _ => false) writes |>in
           let ins := ins <| ins_mem_writes := Some ws |> in
           let s := update_dec_instruction_state iid ins s in
           put s.

      Definition try_commit_store_instruction : itree F (list mem_write_id_t) :=
        s <- get
        ;; '(_, ins, _) <- get_dec_instruction_state iid s
        ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                        "try_commit_store_instruction: no mem writes"
        (* FIXME: check commit-store condition *)
        ;; let wids := List.map write_id ws.(ws_writes) in
           ret wids.

      Definition try_propagate_store_op (wid : mem_write_id_t)
        : itree F (list instruction_id_t) :=
        s <- get
        ;; '(_, ins, subts) <- get_dec_instruction_state iid s
        ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                        "try_propagate_store_op: no mem writes"
        (* ;; guard (isTrue (List.nth_error ws.(ws_has_propagated) wid = Some false)) *)
        ;; w <- try_unwrap_option (List.nth_error ws.(ws_writes) wid)
                                 "try_propagate_store_op: missing wid"
        (* FIXME: check mem-write-propagation condition *)
        ;; 'tt <- trigger (StEWrite w)
        ;; let ws := ws <| ws_has_propagated := list_replace_nth wid true ws.(ws_has_propagated) |> in
           let ins := ins <| ins_mem_writes := Some ws |> in
           (* FIXME: compute iids that need to be restarted *)
           let restarts := [] in
           (* FIXME: let subts := restart_instructions restarts subts in *)
           let s := update_dec_instruction_state_and_subts iid ins subts s in
           'tt <- put s
           ;; ret restarts.

      Definition try_complete_store_ops : itree F unit :=
        (* FIXME: is there anything we need to check here? *)
        let iid := iid in
        ret tt.

    End Handle_instruction_instance.

    Definition handle_E {F}
               `{storageE -< F}
               `{stateE state -< F}
               `{exceptE disabled -< F}
               `{exceptE error -< F}
               `{debugE -< F}
               (iid : instruction_id_t)
      : E ~> itree F :=
      fun A e =>
        let it : itree F A :=
            match e with
            | ThEFetchAndDecodeOrRestart => try_fetch_and_decode_or_restart iid
            | ThEFinishIns => try_finish_instruction iid
            | ThERegAccess _ e => handle_reg_access iid _ e
            (* Load events *)
            | ThEInitMemLoadOps slc => try_init_mem_load_ops iid slc
            | ThESatMemLoadOpForwarding rid => try_sat_mem_load_op_forwarding iid rid
            | ThESatMemLoadOpStorage rid => try_sat_mem_load_op_from_storage iid rid
            | ThECompleteLoadOps => try_complete_load_ops iid
            (* Store events *)
            | ThEInitMemStoreOpFps slc => try_init_mem_store_op_fps iid slc
            | ThEInstaMemStoreOpVals val => try_insta_mem_store_op_vals iid val
            | ThECommitStoreInstruction => try_commit_store_instruction iid
            | ThEPropagateStoreOp wid => try_propagate_store_op iid wid
            | ThECompleteStoreOps => try_complete_store_ops iid
            end in
        'tt <- trigger (Debug ("handle_E: '" ++ show e ++ "'"))
        ;; it.

  End State.
End Make.
