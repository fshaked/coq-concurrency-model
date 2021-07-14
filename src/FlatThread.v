From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Strings.String.

Import ListNotations.

From ExtLib Require Import
     Core.RelDec.

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
(* Typeclasses eauto := 6. *)

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From bbv Require Import Word.
Import Word.Notations.

Require Import Types Utils.
Require Import  Decision.

Module Base (Arc : ArcSig).
  Import Arc.

  Section Denote.
    Variant _E : Type -> Type :=
    | ThEFetchAndDecodeOrRestart : _E (list instruction_id * ast)
    | ThEFinishIns : _E unit
    | ThERegAccess : forall A, regE A -> _E A
    (** Load events *)
    | ThEInitMemLoadOps : mem_slc -> _E (list mem_read_id)
    (* [ThESatMemLoadOpForwarding] returns a bool that indicates if the read
     was fully satisfied, and a list of iids that should be restarted. *)
    | ThESatMemLoadOpForwarding : mem_read_id -> _E (bool * list instruction_id)
    (* [ThESatMemLoadOpStorage] returns a list of iids that should be restarted. *)
    | ThESatMemLoadOpStorage : mem_read_id -> _E (list instruction_id)
    | ThECompleteLoadOps : _E mem_slc_val
    (** Store events *)
    | ThEInitMemStoreOpFps : mem_slc -> _E unit
    | ThEInstaMemStoreOpVals : mem_slc_val -> _E unit
    | ThECommitStoreInstruction : _E (list mem_write_id)
    (* [ThEPropagateStoreOp] returns a list of iids that should be restarted. *)
    | ThEPropagateStoreOp : mem_write_id -> _E (list instruction_id)
    | ThECompleteStoreOps : _E unit.
    (* Workaround: parameter can't be instantiated by an inductive type *)
    Definition E := _E.

    #[global] Instance showable_E : forall A, Showable (E A) :=
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

    Definition lift_regE {F} `{E -< F}
      : regE ~> itree F :=
      fun _ e => trigger (ThERegAccess _ e).

    Definition denote_spawns  {F} `{schedulerE instruction_id -< F}
      : ktree F (list instruction_id) unit :=
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

    Definition denote_restarts {F} `{schedulerE instruction_id -< F}
      : ktree F (list instruction_id) unit :=
      fun iids =>
        List.fold_left
          (fun it iid => Vis (subevent _ (Kill iid)) (fun 'tt => it))
          iids
          (denote_spawns iids).

    Definition lift_mem_read {F}
               `{E -< F} `{chooseE mem_read_id -< F} `{chooseE nat -< F}
               `{schedulerE instruction_id -< F}
               `{exceptE error -< F}
               (slc : mem_slc)
      : itree F mem_slc_val :=
      rids <- trigger (ThEInitMemLoadOps slc)
      ;; ITree.iter (fun rids => (* Reads that aren't fully satisfied yet. *)
                       match rids with
                       | [] =>
                         v <- trigger ThECompleteLoadOps
                         ;; ret (inr v)
                       | _ =>
                         rid <- trigger (Choose rids)
                         ;; let reads := [trigger (ThESatMemLoadOpForwarding rid);
                                         (restarts <- trigger (ThESatMemLoadOpStorage rid)
                                          ;; ret (true, restarts))] in
                            read <- nondet reads
                            ;; read <- try_unwrap_option read
                                                        "lift_mem_read: nondet out of range"
                            ;; is_sat <- exclusive_block
                                          ('(is_sat, restarts) <- read
                                           ;; 'tt <- denote_restarts restarts
                                           ;; ret is_sat)
                            ;; ret (inl (if (is_sat : bool) then
                                           List.remove decision_mem_read_id_eq rid rids
                                         else rids))
                       end) rids.

    Definition lift_mem_write_fp {F} `{E -< F}
               (slc : mem_slc)
      : itree F unit :=
      trigger (ThEInitMemStoreOpFps slc).

    Definition lift_mem_write_val {F}
               `{E -< F} `{chooseE mem_write_id -< F}
               `{schedulerE instruction_id -< F}
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
                         wid <- trigger (Choose wids)
                         ;; 'tt <- exclusive_block
                                    (restarts <- trigger (ThEPropagateStoreOp wid)
                                     ;; denote_restarts restarts)
                         ;; ret (inl (List.remove decision_mem_write_id_eq wid wids))
                       end) wids.

    Definition lift_memE {F}
               `{E -< F} `{chooseE mem_read_id -< F}
               `{chooseE mem_write_id -< F} `{chooseE nat -< F}
               `{schedulerE instruction_id -< F}
               `{exceptE error -< F}
      : memE ~> itree F :=
      fun _ e =>
        match e with
        | MemERead slc => lift_mem_read slc
        | MemEWriteFP slc => lift_mem_write_fp slc
        | MemEWriteVal val => lift_mem_write_val val
        end.

    Definition lift_ins_sem {F}
               `{E -< F} `{chooseE mem_read_id -< F}
               `{chooseE mem_write_id -< F} `{chooseE nat -< F}
               `{schedulerE instruction_id -< F}
               `{exceptE error -< F}
      : itree insSemE ~> itree F :=
      fun _ it =>
        let h := case_ lift_regE lift_memE in
        resum_it _ (interp h it).

    Definition spawn_instruction {F}
               `{schedulerE instruction_id -< F}
               `{wrapE E instruction_id -< F}
               `{chooseE mem_read_id -< F}
               `{chooseE mem_write_id -< F}
               `{chooseE nat -< F}
               `{exceptE error -< F}
               `{debugE -< F}
      : ktree F instruction_id (Types.result unit unit) :=
      fun iid =>
        let it :=
            '(next_iids, ast) <- trigger ThEFetchAndDecodeOrRestart
            ;; 'tt <- denote_spawns next_iids
            ;; 'tt <- resum_it _ (lift_ins_sem _ (denote ast))
            ;; 'tt <- trigger ThEFinishIns
            ;; ret (Accept tt) in
        (* Finnaly, wrap the E events with the iid *)
        resum_it _ (wrap_event_in_it E iid _ it).

    Definition is_eager_event {A T} : (wrapE E T
                                       +' chooseE mem_read_id
                                       +' chooseE mem_write_id
                                       +' chooseE nat
                                       +' exceptE error
                                       +' debugE) A
                                      -> bool :=
      fun e =>
        match e with
        | inl1 (Wrap e _) => (* wrapE E T *)
          match e with
          | ThEFetchAndDecodeOrRestart => true
          | ThEFinishIns => true
          | ThERegAccess _ _ => true
          (** Load events *)
          | ThEInitMemLoadOps slc => true
          | ThESatMemLoadOpForwarding rid => false
          | ThESatMemLoadOpStorage rid => false
          | ThECompleteLoadOps => true
          (** Store events *)
          | ThEInitMemStoreOpFps slc => true
          | ThEInstaMemStoreOpVals val => true
          | ThECommitStoreInstruction => true
          | ThEPropagateStoreOp wid => false
          | ThECompleteStoreOps => true
          end
        | inr1 (inl1 _) => true (* chooseE mem_read_id *)
        | inr1 (inr1 (inl1 _)) => true (* chooseE mem_read_id *)
        | inr1 (inr1 (inr1 (inl1 _))) => true (* chooseE nat *)
        | inr1 (inr1 (inr1 (inr1 (inl1 _)))) (* exceptE error *)
        | inr1 (inr1 (inr1 (inr1 (inr1 _)))) => true (* debugE *)
        end.

    Definition is_eager {R} : itree (schedulerE instruction_id
                                     +' wrapE E instruction_id
                                     +' chooseE mem_read_id
                                     +' chooseE mem_write_id
                                     +' chooseE nat
                                     +' exceptE error
                                     +' debugE) R
                              -> bool :=
      fun it =>
        match observe it with
        | RetF _ => true
        | TauF _ => true
        | @VisF _ _ _ X o k =>
          match o with
          | inl1 e' => true (* schedulerE instruction_id *)
          | inr1 e' => is_eager_event e'
          end
        end.

    Instance RelDec_instruction_id : RelDec (@eq instruction_id) :=
      { rel_dec := fun i1 i2 => isTrue (i1 = i2) }.

    Instance RelDec_instruction_id_Correct: RelDec_Correct RelDec_instruction_id.
    Proof.
      constructor. intros x y.
      unfold rel_dec. simpl.
      unfold isTrue. destruct decide; split; auto.
      intros. discriminate.
    Qed.

    Definition denote {F}
               `{chooseE (instruction_id * bool) -< F}
               `{wrapE E instruction_id -< F}
               `{chooseE mem_read_id -< F}
               `{chooseE mem_write_id -< F}
               `{chooseE nat -< F}
               `{exceptE error -< F}
               `{debugE -< F}
      : ktree F instruction_id (Types.result unit unit) :=
      fun iid =>
        resum_it _ (scheduler spawn_instruction
                              is_eager
                              (fun r1 r2 => match r1, r2 with
                                         | Accept tt, Accept tt => Accept tt
                                         | _, _ => Reject tt
                                         end)
                              (Accept tt)
                              [(iid, spawn_instruction iid)]
                              None).
  End Denote.

  (*****************************************************************************)

  Existing Instance decision_reg_eq.

  Section State.
    Existing Instance showable_ast.
    Existing Instance showable_regE.

    Record reg_read_state :=
      mk_reg_read_state { rrs_slc : reg_slc;
                          rrs_feeding_addr : bool;
                          rrs_reads_from : list (instruction_id * nat * reg_slc_val);
                          (* the [nat] is an index into [ins_reg_writes.rws_slc]
                                                of the instruction pointed by the [instruction_id]. *)
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
                           rws_reg_data_flow : list (instruction_id * nat);
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

    #[global] Instance eta_mem_reads_state : Settable _ :=
      settable! mk_mem_reads_state <rs_footprint; rs_reads; rs_unsat_slcs; rs_reads_from>.

    Instance showable_mem_reads_state : Showable mem_reads_state :=
      { show :=
          fun s => ""%string
      }.

    Record mem_writes_state :=
      mk_mem_writes_state { ws_footprint : mem_slc;
                            ws_writes : list mem_write;
                            ws_has_propagated : list bool }.

    #[global] Instance eta_mem_writes_state : Settable _ :=
      settable! mk_mem_writes_state <ws_footprint; ws_writes; ws_has_propagated>.

    Instance showable_mem_writes_state : Showable mem_writes_state :=
      { show :=
          fun s => ""%string
      }.

    Record decoded_instruction_state :=
      mk_decoded_instruction_state {
          ins_id : instruction_id;
          ins_loc : mem_loc;

          ins_ast : ast;

          ins_reg_reads : list reg_read_state;
          ins_reg_writes : list reg_write_state;

          ins_mem_reads : option mem_reads_state;
          ins_mem_writes : option mem_writes_state;

          ins_finished : bool }.

    #[global] Instance eta_decoded_instruction_state : Settable _ :=
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

    Definition initial_decoded_instruction_state (iid : instruction_id)
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

    Definition ins_tree := (tree decoded_instruction_state
                               (tree (instruction_id * mem_loc) unit))%type.
    Record _state :=
      mk_state { next_iid : instruction_id;
                 instruction_tree : ins_tree }.
    (* Workaround: parameter can't be instantiated by an inductive type *)
    Definition state := _state.

    #[global] Instance eta_state : Settable _ :=
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
  End State.
End Base.

(******************************************************************************)

Module Type ArcThreadSig.
  Declare Module Arc : ArcSig.
  Export Arc.
  Module Base := Base Arc.
  Export Base.

  Parameter  mem_read_request_cand : list decoded_instruction_state ->
                                     decoded_instruction_state -> bool.
End ArcThreadSig.

Require SimpleA64InsSem.

Module SimpleArmv8A : ArcThreadSig with Module Arc := SimpleA64InsSem.Armv8A.
  Module Arc := SimpleA64InsSem.Armv8A.
  Export SimpleA64InsSem.Armv8A.
  Module Base := Base SimpleA64InsSem.Armv8A.
  Export Base.

  Section InstructionKind.
    Variable a : ast.

    Definition is_strong_memory_barrier : bool := (* FIXME: *) let a := a in false.
    Definition is_ld_barrier : bool := (* FIXME: *) let a := a in false.
    Definition is_instruction_barrier : bool := (* FIXME: *) let a := a in false.

    Definition is_load : bool :=
      match a with
      | Load _ _ _ => true
      | _ => false
      end.
    Definition is_store_release : bool := (* FIXME: *) let a := a in false.
    Definition is_load_acquire  : bool := (* FIXME: *) let a := a in false.
  End InstructionKind.

  Section PossibleReadsWrites.
    Variable ins : decoded_instruction_state.

    Definition read_initiated : bool := isTrue (ins.(ins_mem_reads) <> None).

    Definition read_completed : bool :=
      match ins.(ins_mem_reads) with
      | Some reads => forallb (fun u => isTrue (u = nil))
                             reads.(rs_unsat_slcs)
      | None => false
      end.

    (* Definition read_requested rr : bool := *)
    (*   List.lookup rr inst.subreads.sr_requested <> Nothing. *)


    (* (* Return Nothing if the read footprint is not determined yet, or Just *)
     (*    applied to the set of read addresses otherwise. If the memory read *)
     (*    has already been initiated then this information is in the *)
     (*    instruction instance state; if not, the footprint is only *)
     (*    determined if the instruction has a Mem_read outcome in the next *)
     (*    state. (This depends on the fact that the only register in the Sail *)
     (*    code for loads is for determining the data, after that the read can *)
     (*    go ahead. *) *)
    (* let read_footprint_of_load instruction : maybe footprint = *)
    (*   match instruction.subreads.sr_addr with *)
    (*   | Just fp -> Just fp *)
    (*   | Nothing -> *)
    (*       match instruction.micro_op_state with *)
    (*       | MOS_plain (O_Read_mem (read_kind,addr_lifted,size) _) -> *)
    (*          let addr = ensure_just (address_of_address_lifted addr_lifted) *)
    (*                       "read_footprint_of_load: bad address" in *)
    (*          Just (addr, size) *)
    (*       | _ ->  Nothing *)
    (*       end *)
    (*   end *)


    (* let possibly_reads_address *)
    (*     (instruction: instruction_instance 'i) *)
    (*     (fps:         set footprint) *)
    (*     : bool *)
    (*   = *)
    (*   is_memory_load_instruction (ik instruction) && *)
    (*   match read_footprint_of_load instruction with *)
    (*   | Just fp -> non_empty_intersection_set fps {fp} *)
    (*   | Nothing -> exists ((_, s) IN fps). s <> 0 *)
    (*   end *)


    (* let possibly_writes_address *)
    (*     (instruction: instruction_instance 'i) *)
    (*     (fps:         set footprint) *)
    (*     : bool *)
    (*   = *)
    (*   is_viable_memory_store_ii instruction && *)
    (*   match instruction.subwrites.sw_addr with *)
    (*   | Just fp -> non_empty_intersection_set fps {fp} *)
    (*   | Nothing -> exists ((_, s) IN fps). s <> 0 *)
    (*   end *)


    (* (* Return 'true' iff 'instruction' might read or write from/to a footprint *)
     (* intersecting with 'fps'. In particular, return 'true' if the footprint of *)
     (* 'instruction' can't be determined. *)
     (* NOTE: we check the instruction in its current state, i.e., if the *)
     (* pseudocode has not made enough steps yet to make the reads/writes avilable *)
     (* the function returns 'true' for any (non-empty) 'fps', and we don't consider *)
     (* what can happen if the instruction is restarted. *) *)
    (* let possibly_reads_or_writes_address *)
    (*     (inst: instruction_instance 'i) *)
    (*     (fps:  set footprint) *)
    (*     : bool *)
    (*   = *)
    (*   possibly_reads_address inst fps || possibly_writes_address inst fps *)

    (* return true iff the sail code has already generated its memory-read event for *)
    (*    the instruction. This guarantees that the instruction's memory read is *)
    (*    recorded in the instruction_instance state. *)
    Definition all_reads_are_calculated : bool :=
      is_load ins.(ins_ast)
                    ---> read_initiated.

    (* let all_writes_are_calculated inst : bool = *)
    (*   is_viable_memory_store_ii inst --> write_initiated inst *)

    (* (* return true iff the sail code has already generated all the memory-read/write *)
     (*    events (except AArch64 write-mem-value, i.e., E_write_memv) for the *)
     (*    instruction. This guarantees that any memory read/write footprint of the *)
     (*    instruction is recorded in the instruction_instance state. *) *)
    (* let all_writes_reads_are_calculated inst : bool = *)
    (*   (* for efficiency, first check if 'inst' is unfinished *) *)
    (*   inst.finished || *)
    (*   (all_reads_are_calculated inst && all_writes_are_calculated inst) *)

    Definition is_entirely_satisfied_load : bool :=
      all_reads_are_calculated
      && read_completed.

    Definition finished_load_part : bool :=
      ins.(ins_finished). (* || ins.rmw_finished_load_snapshot <> Nothing *)
  End PossibleReadsWrites.




  Open Scope bool_scope.
  (* LEM: machineDefThreadSubsystem.lem: pop_memory_read_request_cand *)
  Definition mem_read_request_cand (pref : list decoded_instruction_state)
             (ins : decoded_instruction_state) : bool :=
    (* NOTE: we don't check that po-preceding instructions to the same
                 address are finished.
                 See also private comment THREAD1 *)
    (forallb (fun prev_ins =>
               is_strong_memory_barrier prev_ins.(ins_ast)
               ---> prev_ins.(ins_finished))
            pref) &&

    (* See private comment THREAD2 *)
    (forallb (fun prev_ins =>
               is_instruction_barrier prev_ins.(ins_ast)
               ---> prev_ins.(ins_finished))
            pref) &&

    (* barrier.st/ld: *)
    (forallb (fun prev_ins =>
               is_ld_barrier prev_ins.(ins_ast)
               ---> prev_ins.(ins_finished))
            pref) &&

    (* load-acquire/store-release (RCsc):
           A store-release and a po-succeeding load-acquire are observed in
           program order *)
    (is_load_acquire ins.(ins_ast)
     ---> forallb (fun prev_ins =>
                 is_store_release prev_ins.(ins_ast)
                 ---> prev_ins.(ins_finished))
              pref) &&

    (* All po-preceding load-acquires must issue their requests before the
         read request.
         Also see private note THREAD3 *)
    (forallb (fun prev_ins =>
               is_load_acquire prev_ins.(ins_ast)
               ---> (finished_load_part prev_ins ||
                  is_entirely_satisfied_load prev_ins))
            pref).

End SimpleArmv8A.

(******************************************************************************)

Module Make (Arc : ArcSig) (ArcThread : ArcThreadSig with Module Arc := Arc) : ThreadSig Arc.
  Export ArcThread.

  Definition state := state.
  Definition showable_state := showable_state.
  Definition E := E.
  Definition showable_E := showable_E.
  Definition is_eager_event {A T} := @is_eager_event A T.
  Definition denote {F} := @denote F.

  Definition initial_state '((InstructionID iid) : instruction_id) (loc : mem_loc)
    : state :=
    {| next_iid := InstructionID (iid + 1);
       instruction_tree := TLeaf (TNode (InstructionID iid, loc) []) |}.

  Section RegisterRead.
    Local Instance slice_id_rsv : Slice (instruction_id * nat * reg_slc_val) :=
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
             (rf : list (instruction_id * nat * reg_slc_val))
      : option (list (instruction_id * nat * reg_slc_val)) :=
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
                                (InstructionID 0, 0, {| rsv_slc := rslc;
                                                        rsv_val :=
                                                          Some (wzero rslc.(rs_size)) |})::rf)
                             rslcs
                             rf)
      end.

    Program Definition reg_val_of_reads_from (slc : reg_slc)
            (rf : list ((instruction_id * nat) * reg_slc_val))
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
           (iid : instruction_id)
           (pref : list decoded_instruction_state)
           (t : ins_tree)
    : option (list decoded_instruction_state * mem_loc *
              list (tree (instruction_id * mem_loc) unit)) :=
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
             (iid : instruction_id) (s : state)
    : option (list decoded_instruction_state * mem_loc *
              list (tree (instruction_id * mem_loc) unit)) :=
    get_first_unfetched_instruction_helper iid [] s.(instruction_tree).

  Fixpoint get_dec_instruction_state_helper
           (iid : instruction_id)
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
             (iid : instruction_id) (s : state)
    : option (list decoded_instruction_state *
              decoded_instruction_state *
              list ins_tree) :=
    get_dec_instruction_state_helper iid [] s.(instruction_tree).

  Definition try_get_dec_instruction_state {F}
             `{exceptE error -< F}
             (iid : instruction_id) (s : state)
    : itree F (list decoded_instruction_state *
               decoded_instruction_state *
               list ins_tree) :=
    try_unwrap_option (get_dec_instruction_state iid s)
                      ("try_get_dec_instruction_state: missing iid " ++ show iid).

  Definition update_dec_instruction_state_and_subts
             (iid : instruction_id) (dins : decoded_instruction_state)
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
             (iid : instruction_id) (dins : decoded_instruction_state)
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

    Variable iid : instruction_id.

    Definition try_fetch_and_decode_or_restart
      : itree F (list instruction_id * ast) :=
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
              let '(InstructionID niid) := s.(next_iid) in
              let iids :=
                  List.map InstructionID
                           (List.seq niid (List.length next_pcs)) in
              let subts := List.map (fun '(iid, pc) => TLeaf (TNode (iid, pc) []))
                                    (List.combine iids next_pcs) in
              let s := s <| next_iid := InstructionID (niid + (List.length next_pcs)) |> in
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
      : itree F (list mem_read_id) :=
      s <- get
      ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
      ;; let sub_slcs := split_load_mem_slc ins.(ins_ast) slc in
         let kind := mem_read_kind_of_ast ins.(ins_ast) in
         let rids := List.map MemReadID
                              (List.seq 0 (List.length sub_slcs)) in
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


    Definition try_sat_mem_load_op_forwarding (rid : mem_read_id)
      : itree F (bool * list instruction_id) :=
      (* FIXME: *)
      let iid := iid in
      guard false
      ;; ret (false, []).

    Definition restart_instructions (iids : list instruction_id)
               (ts : list ins_tree)
      : list ins_tree :=
      List.map (tree_map
                  (fun ins => if decide (In ins.(ins_id) iids) then
                             (initial_decoded_instruction_state iid ins.(ins_loc) ins.(ins_ast))
                           else ins)
                  (fun l => l))
               ts.

    Definition try_sat_mem_load_op_from_storage '((MemReadID rid) : mem_read_id)
      : itree F (list instruction_id) :=
      s <- get
      ;; '(pref, ins, subts) <- try_get_dec_instruction_state iid s
      ;; 'tt <- guard (ArcThread.mem_read_request_cand pref ins)
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
                         (fun '(wid, (slc, val)) => {| write_id := MemWriteID wid;
                                                    write_footprint := slc;
                                                    write_val := val;
                                                    write_kind := kind |})
                         (List.combine wids sub_slcs) in
         let ws := ws <| ws_writes := writes |>
                                             <| ws_has_propagated := List.map (fun _ => false) writes |>in
         let ins := ins <| ins_mem_writes := Some ws |> in
         let s := update_dec_instruction_state iid ins s in
         put s.

    Definition try_commit_store_instruction : itree F (list mem_write_id) :=
      s <- get
      ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
      ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                      "try_commit_store_instruction: no mem writes"
      (* FIXME: check commit-store condition *)
      ;; let wids := List.map write_id ws.(ws_writes) in
         ret wids.

    Definition try_propagate_store_op '((MemWriteID wid) : mem_write_id)
      : itree F (list instruction_id) :=
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
             (iid : instruction_id)
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
End Make.
