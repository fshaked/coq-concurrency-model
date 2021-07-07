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
  Existing Instance showable_ast.
  Existing Instance decision_reg_eq.
  Existing Instance showable_regE.

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
                | ThEFetchAndDecodeOrRestart => "ThEFetchAndDecodeOrRestart"
                | ThEFinishIns => "ThEFinishIns"
                | ThERegAccess _ e => "ThERegAccess (" ++ show e ++ ")"
                (** Load events *)
                | ThEInitMemLoadOps slc => "ThEInitMemLoadOps " ++ show slc
                | ThESatMemLoadOpForwarding rid => "ThESatMemLoadOpForwarding " ++ show rid
                | ThESatMemLoadOpStorage rid => "ThESatMemLoadOpStorage " ++ show rid
                | ThECompleteLoadOps => "ThECompleteLoadOps"
                (** Store events *)
                | ThEInitMemStoreOpFps slc => "ThEInitMemStoreOpFps " ++ show slc
                | ThEInstaMemStoreOpVals val => "ThEInstaMemStoreOpVals " ++ show val
                | ThECommitStoreInstruction => "ThECommitStoreInstruction"
                | ThEPropagateStoreOp wid => "ThEPropagateStoreOp " ++ show wid
                | ThECompleteStoreOps => "ThECompleteStoreOps"
                end%string
    }.

  Section Denote.
    Definition lift_regE {F} `{E -< F}
    : regE ~> itree F :=
      fun _ e => trigger (ThERegAccess _ e).

    Definition denote_spawns  {F} `{schedulerE instruction_id_t -< F}
      : ktree F (list instruction_id_t) unit :=
      fun iids =>
        List.fold_left
          (fun it iid => Vis (subevent _ (Spawn iid)) (fun 'tt => it))
          iids (Ret tt).
        (* The fold above can also be implemented as below. I'm not sure which
           way is better. The implementation above has less [Tau]s, and
           therefore less nondet interleaving, but that is not a big factor. *)
        (* ITree.iter (fun iids => *)
        (*               match iids with *)
        (*               | [] => ret (inr tt) *)
        (*               | iid::iids => 'tt <- trigger (Spawn iid) *)
        (*                            ;; ret (inl iids) *)
        (*               end) iids. *)

    Definition denote_restarts {F} `{schedulerE instruction_id_t -< F}
      : ktree F (list instruction_id_t) unit :=
      fun iids =>
        'tt <- trigger (Kill iids)
        ;; denote_spawns iids.


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
            '(next_iids, ast) <- trigger ThEFetchAndDecodeOrRestart
            ;; 'tt <- denote_spawns next_iids
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
                              (fun _ _ => false)
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

    Local Open Scope string_scope.
    Instance showable_reg_read_state : Showable reg_read_state :=
      { show :=
          fun s => show s.(rrs_slc) ++ " = " ++
                                 match s.(rrs_val) with
                                 | Some v => show v
                                 | None => "?"
                                 end
      }.
    Close Scope string_scope.

    Record reg_write_state :=
      mk_reg_write_state { rws_slc_val : reg_slc_val;
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

    Instance showable_reg_write_state : Showable reg_write_state :=
      { show := fun s => show s.(rws_slc_val) }.

    Record mem_reads_state :=
      mk_mem_reads_state { rs_footprint : mem_slc;
                           rs_reads : list mem_read;
                           rs_unsat_slcs : list (list mem_slc);
                           rs_reads_from : list mem_reads_from }.

    Instance eta_mem_reads_state : Settable _ :=
      settable! mk_mem_reads_state <rs_footprint; rs_reads; rs_unsat_slcs; rs_reads_from>.

    Instance showable_mem_reads_state : Showable mem_reads_state :=
      { show :=
          fun s => ""%string
      }.

    Record mem_writes_state :=
      mk_mem_writes_state { ws_footprint : mem_slc;
                            ws_writes : list mem_write;
                            ws_has_propagated : list bool }.

    Instance eta_mem_writes_state : Settable _ :=
      settable! mk_mem_writes_state <ws_footprint; ws_writes; ws_has_propagated>.

    Instance showable_mem_writes_state : Showable mem_writes_state :=
      { show :=
          fun s => ""%string
      }.

    Record decoded_instruction_state :=
      mk_decoded_instruction_state {
          ins_id : instruction_id_t;
          ins_loc : mem_loc;

          ins_ast : ast;

          ins_reg_reads : list reg_read_state;
          ins_reg_writes : list reg_write_state;

          ins_mem_reads : option mem_reads_state;
          ins_mem_writes : option mem_writes_state;

          ins_finished : bool }.

    Instance eta_decoded_instruction_state : Settable _ :=
      settable! mk_decoded_instruction_state <ins_id; ins_loc; ins_ast; ins_reg_reads; ins_reg_writes; ins_mem_reads; ins_mem_writes; ins_finished>.

    Local Open Scope string_scope.
    Instance showable_decoded_instruction_state : Showable decoded_instruction_state :=
      { show :=
          fun i =>
            show i.(ins_id) ++ ":[" ++ show i.(ins_loc) ++ "] " ++
              ("'" ++ show i.(ins_ast) ++ "' " ++
                                       (if i.(ins_finished) then "(finished)"
                                        else "(in-flight)") ++ newline ++
             match i.(ins_reg_reads) with
             | [] => ""
             | _ => "  reg reads: " ++ show i.(ins_reg_reads) ++ newline
             end ++
             match i.(ins_reg_writes) with
             | [] => ""
             | _ => "  reg writes: " ++ show i.(ins_reg_writes) ++ newline
             end ++
             match i.(ins_mem_reads) with
             | Some rs => "  mem reads: " ++ show rs ++ newline
             | None => ""
             end ++
             match i.(ins_mem_writes) with
             | Some ws => "  mem writes: " ++ show ws ++ newline
             | None => ""
             end
            )%string
      }.
    Close Scope string_scope.

    Definition initial_decoded_instruction_state (iid : instruction_id_t)
               (loc : mem_loc) (ast : ast)
      : decoded_instruction_state :=
      let info := info_of_ast ast in
      {| ins_id := iid;
         ins_loc := loc;

         ins_ast := ast;

         ins_reg_reads := List.map (fun '(slc, addr) => mk_reg_read_state slc addr [] None)
                                   info.(input_regs);
         ins_reg_writes := List.map (fun slc => mk_reg_write_state
                                               {| rsv_slc := slc; rsv_val := None |}
                                               [] false)
                                    info.(output_regs);
         ins_mem_reads := None;
         ins_mem_writes := None;
         ins_finished := false |}.

    Notation ins_tree := (tree decoded_instruction_state
                               (tree (instruction_id_t * mem_loc) unit))%type.
    Record _state :=
      mk_state { next_iid : instruction_id_t;
                 instruction_tree : ins_tree }.
    (* Workaround: parameter can't be instantiated by an inductive type *)
    Definition state := _state.

    Instance eta_state : Settable _ :=
      settable! mk_state <next_iid; instruction_tree>.

    Local Open Scope string_scope.
    Instance showable_state : Showable state :=
      { show :=
          fun s =>
            let fix show_unf_tree t :=
                match t with
                | TLeaf tt => ""
                | TNode (iid, _) [] => show iid
                | TNode (iid, _) [t] => (show iid) ++ "," ++ show_unf_tree t
                | TNode (iid, _) ts =>
                  (show iid) ++ "["
                             ++ String.concat ";" (List.map show_unf_tree ts)
                             ++ "]"
                end in
            let fix show_dec_tree t :=
                match t with
                | TLeaf t => show_unf_tree t
                | TNode i [] => show i.(ins_id)
                | TNode i [t] => (show i.(ins_id)) ++ "," ++ show_dec_tree t
                | TNode i ts =>
                  (show i.(ins_id)) ++ "["
                             ++ String.concat ";" (List.map show_dec_tree ts)
                             ++ "]"
                end in
            let show_ins i :=
                match i with
                | inl i => show i
                | inr t =>
                  let show_ins i :=
                      match i with
                      | inl (iid, loc) =>
                        show iid ++ ":[" ++ show loc ++ "] not fetched"
                      | inr tt => ""
                      end in
                  String.concat "" (List.map show_ins (tree_to_list_preorder t))
                end in
            "Instruction tree: " ++ newline ++
            "  " ++ (show_dec_tree s.(instruction_tree)) ++ newline ++
            "Instructions:" ++ newline ++
            String.concat "" (List.map show_ins (tree_to_list_preorder s.(instruction_tree)))
      }.
    Close Scope string_scope.

    Definition initial_state (iid : instruction_id_t) (loc : mem_loc)
      : state :=
      {| next_iid := iid + 1;
         instruction_tree := TLeaf (TNode (iid, loc) []) |}.

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
               (r : reg)
               (rslcs : list reg_slc)
               (pref : list decoded_instruction_state)
               (rf : list (instruction_id_t * nat * reg_slc_val))
        : option (list (instruction_id_t * nat * reg_slc_val)) :=
        match pref with
        | ins::pref =>
          let wslcs := List.combine (List.seq 0 (List.length ins.(ins_reg_writes)))
                                    ins.(ins_reg_writes) in
          let wslcs := List.filter (fun '(i, w) => isTrue (w.(rws_slc_val).(rsv_slc).(rs_reg) = r))
                                   wslcs in
          let wslcs := List.map (fun '(i, w) => ((ins.(ins_id), i), w.(rws_slc_val))) wslcs in

          match Utils.reads_from_slcs wslcs rslcs rf with
          | Some (rf, nil) => Some rf
          | Some (rf, rslcs) => read_reg_slcs r rslcs pref rf
          | None => None
          end
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

    Fixpoint get_first_unfetched_instruction_helper
             (iid : instruction_id_t)
             (pref : list decoded_instruction_state)
             (t : ins_tree)
      : option (list decoded_instruction_state * mem_loc *
                list (tree (instruction_id_t * mem_loc) unit)) :=
      match t with
      | TNode i ts =>
        match List.find (fun x => isTrue (~(x = None)))
                        (List.map (get_first_unfetched_instruction_helper iid (i::pref)) ts)
        with
        | Some x => x
        | None => None
        end
      | TLeaf (TNode (iid', loc) ts) =>
        if decide (iid' = iid) then Some (pref, loc, ts)
        else None
      | TLeaf _ => None
      end.

    Definition get_first_unfetched_instruction
               (iid : instruction_id_t) (s : state)
      : option (list decoded_instruction_state * mem_loc *
                list (tree (instruction_id_t * mem_loc) unit)) :=
      get_first_unfetched_instruction_helper iid [] s.(instruction_tree).

    Fixpoint get_dec_instruction_state_helper
               (iid : instruction_id_t)
               (pref : list decoded_instruction_state)
               (t : ins_tree)
      : option (list decoded_instruction_state *
                decoded_instruction_state *
                list ins_tree) :=
      match t with
      | TNode i ts =>
        if decide (i.(ins_id) = iid) then Some (pref, i, ts)
        else
          match List.find (fun x => isTrue (~(x = None)))
                          (List.map (get_dec_instruction_state_helper iid (i::pref)) ts)
          with
          | Some x => x
          | None => None
          end
      | TLeaf _ => None
      end.

    Definition get_dec_instruction_state
               (iid : instruction_id_t) (s : state)
      : option (list decoded_instruction_state *
                decoded_instruction_state *
                list ins_tree) :=
      get_dec_instruction_state_helper iid [] s.(instruction_tree).

    Definition try_get_dec_instruction_state {F}
               `{exceptE error -< F}
               (iid : instruction_id_t) (s : state)
      : itree F (list decoded_instruction_state *
                 decoded_instruction_state *
                 list ins_tree) :=
      try_unwrap_option (get_dec_instruction_state iid s)
                        ("try_get_dec_instruction_state: missing iid " ++ show iid).

    Definition update_dec_instruction_state_and_subts
               (iid : instruction_id_t) (dins : decoded_instruction_state)
               (ts : list ins_tree) (s : state)
      : state :=
      let fix helper t :=
          match t with
          | TNode i ts' =>
            if decide (i.(ins_id) = iid) then TNode dins ts
            else TNode i (List.map helper ts')
          | TLeaf (TNode (iid', _) _) =>
            if decide (iid' = iid) then TNode dins ts
            else t
          | TLeaf (TLeaf tt) => t
          end in
      s <| instruction_tree := helper s.(instruction_tree) |>.

    Definition update_dec_instruction_state
               (iid : instruction_id_t) (dins : decoded_instruction_state)
               (s : state)
      : state :=
      let fix helper t :=
          match t with
          | TNode i ts' =>
            if decide (i.(ins_id) = iid) then TNode dins ts'
            else TNode i (List.map helper ts')
          | TLeaf (TNode (iid', _) ts') =>
            if decide (iid' = iid) then TNode dins (List.map TLeaf ts')
            else t
          | TLeaf (TLeaf tt) => t
          end in
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
        ;; match get_dec_instruction_state iid s with
           | Some (_, ins, _) =>
             (* Nothing to do, the instruction-state has already been restarted. *)
             ret ([], ins.(ins_ast))
           | None =>
             '(_, loc, _) <- guard_some (get_first_unfetched_instruction iid s)
             ;; '(slc, rf) <- trigger (StEReadInstruction loc)
             ;; val <- try_unwrap_option (mem_slc_val_of_reads_from slc rf)
                                        "try_fetch_and_decode_or_restart: some bytes are missing from memory read of instruction."
             ;; ast <- try_unwrap_option (decode val)
                                        "try_fetch_and_decode_or_restart: decoding of instruction failed"
             ;; let ins := initial_decoded_instruction_state iid loc ast in
                let next_pcs := next_pc loc ast in
                let iids := List.seq s.(next_iid) (List.length next_pcs) in
                let subts := List.map (fun '(iid, pc) => TLeaf (TNode (iid, pc) []))
                                      (List.combine iids next_pcs) in
                let s := s <| next_iid := s.(next_iid) + (List.length next_pcs) |> in
                let s := update_dec_instruction_state_and_subts iid ins subts s in
                'tt <- put s
             ;; ret (iids, ast)
           end.

      Definition try_finish_instruction : itree F unit :=
        (* FIXME: check finish condition *)
        s <- get
        ;; '(pref, ins, _) <- try_get_dec_instruction_state iid s
        ;; let ins := ins <| ins_finished := true |> in
           let s := update_dec_instruction_state iid ins s in
           put s.

      Definition try_read_reg_slc (rslc : reg_slc)
        : itree F (reg_val rslc.(rs_size)) :=
        s <- get
        ;; '(pref, ins, _) <- try_get_dec_instruction_state iid s
        ;; match read_reg_slcs rslc.(rs_reg) [rslc] pref [] with
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
        ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
        ;; let reg_writes :=
               List.map
                 (fun rws =>
                    if decide (rws.(rws_slc_val).(rsv_slc) = rslc) then
                      let rdf := List.concat (List.map (fun rrs => List.map fst rrs.(rrs_reads_from))
                                                       ins.(ins_reg_reads)) in
                      let mdf := match ins.(ins_mem_reads) with Some _ => true | _ => false end in
                      mk_reg_write_state {| rsv_slc := rslc; rsv_val := Some val |}
                                         rdf mdf
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
        ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
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
        guard false
        ;; ret (false, []).

      Definition restart_instructions (iids : list instruction_id_t)
                 (ts : list ins_tree)
        : list ins_tree :=
        List.map (tree_map
                    (fun ins => if decide (In ins.(ins_id) iids) then
                               (initial_decoded_instruction_state iid ins.(ins_loc) ins.(ins_ast))
                             else ins)
                    (fun l => l))
                 ts.

      (* Notation "'forall' ( x 'MEM' l ), p" := (Forall (fun x => p) l) *)
      (*                                           (at level 40) : . *)
      (* Notation "'forall' ( ' x  'MEM' l ), p" := (Forall (fun x => p) l) *)
      (*                                         (x pattern, at level 40). *)

      Infix "-->" := implb (at level 51, right associativity)
                     : bool_scope.
      (* LEM: machineDefThreadSubsystem.lem: pop_memory_read_request_cand *)
  (*     Definition mem_read_request_cand pref i : Prop := *)
  (*       (* NOTE: we don't check po-previous instructions to the same address. *)
  (*          See also private comment THREAD1 *) *)
  (*       (forallb (fun `(_, _, prev_ins) => *)
  (*                     is_strong_memory_barrier prev_ins.(ins_ast) *)
  (*                     --> prev_inst.(ins_finished)) *)
  (*               pref) *)

  (*       (forall (prev_inst MEM pref), *)
  (*          is_pop_strong_memory_barrier prev_inst.(ins_ast) --> prev_inst.(ins_finished)) && *)

  (* (* See private comment THREAD2 *) *)
  (* (forall (prev_inst MEM inst_context.active_prefix). *)
  (*      is_pop_instruction_barrier (ik prev_inst) --> prev_inst.finished) && *)

  (* (* Additions for barrier.st/ld: *) *)
  (* (forall (prev_inst MEM inst_context.active_prefix). *)
  (*     is_AArch64_ld_barrier (ik prev_inst) --> prev_inst.finished) && *)

  (* (* Additions for load.acquire/store.release: *) *)
  (* (* A Store-Release followed by a Load-Acquire is observed in program order *) *)
  (* ((is_AArch64_load_acquire (ik instruction) || *)
  (*   is_RISCV_load_strong_acquire (ik instruction)) --> *)
  (*     forall (prev_inst MEM inst_context.active_prefix). *)
  (*         (is_AArch64_store_release (ik prev_inst) || *)
  (*          is_RISCV_store_strong_release (ik prev_inst)) *)
  (*         --> prev_inst.finished) && *)

  (* (* All po-previous Load-acquires must issue their requests before the *)
  (* read request. Also see private note THREAD3 *) *)
  (* (forall (prev_inst MEM inst_context.active_prefix). *)
  (*     (is_AArch64_load_acquire (ik prev_inst) || *)
  (*        is_RISCV_load_acquire (ik prev_inst)) *)
  (*     --> *)
  (*     (finished_load_part prev_inst || *)
  (*     is_entirely_satisfied_load prev_inst)) && *)

  (* (* Additions for lwsync: *) *)
  (* (* all loads that are po-followed by lwsync in active_prefix are finished *) *)
  (* List.dropWhile (fun i -> not (is_lwsync (ik i))) inst_context.active_prefix *)
  (* $> List.dropWhile (fun i -> is_memory_load_instruction (ik i) --> finished_load_part i) *)
  (* $> List.null && *)

  (* (* Additions for load-reserve/store-conditional: *) *)
  (* (is_PPC_load_reserve (ik instruction) --> *)
  (*     forall (prev_inst MEM inst_context.active_prefix). *)
  (*         (is_PPC_load_reserve (ik prev_inst) || is_PPC_store_conditional (ik prev_inst)) *)
  (*         --> prev_inst.finished) && *)

  (* (*** Additions for RISCV fences ***) *)
  (* (forall_iprev_with_prefix inst_context.active_prefix $ fun prev_inst prev_active_prefix -> *)
  (*     is_RISCV_fence_sr (ik prev_inst) --> *)
  (*       (prev_inst.finished || *)
  (*       (is_RISCV_fence_pr (ik prev_inst) *)
  (*         && not (is_RISCV_fence_pw (ik prev_inst)) *)
  (*         && forall (prev_prev_inst MEM prev_active_prefix). *)
  (*               is_memory_load_instruction (ik prev_prev_inst) *)
  (*                 --> is_entirely_satisfied_load prev_prev_inst))) && *)

  (* (forall_iprev_with_prefix inst_context.active_prefix $ fun prev_inst prev_active_prefix -> *)
  (*     is_RISCV_fence_tso (ik prev_inst) --> *)
  (*       (prev_inst.finished || *)
  (*       forall (prev_prev_inst MEM prev_active_prefix). *)
  (*           is_memory_load_instruction (ik prev_prev_inst) *)
  (*             --> is_entirely_satisfied_load prev_prev_inst)) && *)

  (* (*** Additions for RISCV load-release/store-acquire ***) *)
  (* (is_RISCV_load_release (ik instruction) --> *)
  (*     forall (prev_inst MEM inst_context.active_prefix). prev_inst.finished) && *)
  (* (forall (prev_inst MEM inst_context.active_prefix). *)
  (*     is_RISCV_store_acquire (ik prev_inst) --> prev_inst.finished) *)



      Definition try_sat_mem_load_op_from_storage (rid : mem_read_id_t)
        : itree F (list instruction_id_t) :=
        s <- get
        ;; '(_, ins, subts) <- try_get_dec_instruction_state iid s
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
                        <| rs_reads_from := list_replace_nth rid (rf_forward ++ rf_storage)
                                                             rs.(rs_reads_from) |> in
           let ins := ins <| ins_mem_reads := Some rs |> in
           (* FIXME: compute iids that need to be restarted *)
           let restarts :=
               (List.fold_left (fun iids t =>
                                  List.fold_left (fun iids i =>
                                                    match i with
                                                    | inl ins =>
                                                      if ins.(ins_finished) then iids
                                                      else ins.(ins_id) :: iids
                                                    | inr _ => iids
                                                    end)
                                                 (tree_to_list_preorder t)
                                                 iids)
                               subts
                               []) in
           let subts := restart_instructions restarts subts in
           let s := update_dec_instruction_state_and_subts iid ins subts s in
           'tt <- put s
           ;; ret restarts.

      Definition try_complete_load_ops : itree F mem_slc_val :=
        s <- get
        ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
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
        ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
        ;; let ws := {| ws_footprint := slc;
                        ws_writes := [];
                        ws_has_propagated := [] |} in
           let ins := ins <| ins_mem_writes := Some ws |> in
           let s := update_dec_instruction_state iid ins s in
           put s.

      Definition try_insta_mem_store_op_vals (val : mem_slc_val) : itree F unit :=
        s <- get
        ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
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
        ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
        ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                        "try_commit_store_instruction: no mem writes"
        (* FIXME: check commit-store condition *)
        ;; let wids := List.map write_id ws.(ws_writes) in
           ret wids.

      Definition try_propagate_store_op (wid : mem_write_id_t)
        : itree F (list instruction_id_t) :=
        s <- get
        ;; '(_, ins, subts) <- try_get_dec_instruction_state iid s
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
           let restarts :=
               (List.fold_left (fun iids t =>
                                  List.fold_left (fun iids i =>
                                                    match i with
                                                    | inl ins =>
                                                      if ins.(ins_finished) then iids
                                                      else ins.(ins_id) :: iids
                                                    | inr _ => iids
                                                    end)
                                                 (tree_to_list_preorder t)
                                                 iids)
                               subts
                               []) in
           let subts := restart_instructions restarts subts in
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
        'tt <- trigger (Debug ("handle_E: " ++ show e))
        ;; it.

  End State.
End Make.
