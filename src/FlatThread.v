From Coq Require Import
     Arith.PeanoNat
     Lists.List
     MSets.MSetAVL
     NArith.NArith
     Strings.String
     Structures.OrdersEx.

Import ListNotations.

From ExtLib Require Import
     Core.RelDec
     Data.Monads.ListMonad
     Monads.

Import MonadNotation.

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
     Events.State.

Import Monads.
Import ITreeNotations.

Open Scope monad_scope.

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

Module NatSet := MSetAVL.Make Nat_as_OT.

Module Base (Arc : ArcSig).
  Export Arc.

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
    | ThECompleteStoreOps : _E unit
    (** Barrier events *)
    | ThEBarrier : forall A, barE A -> _E A.
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
                  | ThEBarrier _ e => "ThEBarrier (" ++ show e ++ ")"
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
                         rid <- trigger (Choose "mem read of load" rids)
                         ;; let reads := [trigger (ThESatMemLoadOpForwarding rid);
                                         (restarts <- trigger (ThESatMemLoadOpStorage rid)
                                          ;; ret (true, restarts))] in
                            read <- nondet "mem read source" reads
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
                         wid <- trigger (Choose "mem write of store" wids)
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

    Definition lift_barE {F}
               `{E -< F}
               `{exceptE error -< F}
      : barE ~> itree F :=
      fun _ e => trigger (ThEBarrier _ e).

    Definition lift_ins_sem {F}
               `{E -< F} `{chooseE mem_read_id -< F}
               `{chooseE mem_write_id -< F} `{chooseE nat -< F}
               `{schedulerE instruction_id -< F}
               `{exceptE error -< F}
      : itree insSemE ~> itree F :=
      fun _ it =>
        let h := case_ lift_regE (case_ lift_memE lift_barE) in
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
          (** Barrier events *)
          | ThEBarrier _ _ => true
          end
        | inr1 (inl1 _) => true (* chooseE mem_read_id *)
        | inr1 (inr1 (inl1 _)) => true (* chooseE mem_write_id *)
        | inr1 (inr1 (inr1 (inl1 _))) => true (* chooseE nat *)
        | inr1 (inr1 (inr1 (inr1 (inl1 _)))) => true (* exceptE error *)
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
        resum_it _ (scheduler "schedule instructions"
                              spawn_instruction
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
                          (* the [nat] is an index into [ins_reg_writes] of the
                             instruction pointed by the [instruction_id]. *)
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

    Local Open Scope string_scope.
    Instance showable_mem_reads_state : Showable mem_reads_state :=
      { show :=
          fun s =>
            String.concat newline
                          (List.map (fun '(r, uslcs, rf) =>
                                       ("    " ++ show r)
                                         ++ (if decide (uslcs = []) then ""
                                             else " unsat slices: " ++ show uslcs)
                                         ++ (if decide (rf = []) then ""
                                             else " rf: " ++ newline ++ show rf))
                                    (List.combine (List.combine s.(rs_reads)
                                                                    s.(rs_unsat_slcs))
                                                  s.(rs_reads_from)))
      }.
    Close Scope string_scope.

    Record mem_writes_state :=
      mk_mem_writes_state { ws_footprint : mem_slc;
                            ws_writes : list mem_write;
                            ws_has_propagated : list bool }.

    #[global] Instance eta_mem_writes_state : Settable _ :=
      settable! mk_mem_writes_state <ws_footprint; ws_writes; ws_has_propagated>.

    Local Open Scope string_scope.
    Instance showable_mem_writes_state : Showable mem_writes_state :=
      { show :=
          fun s => String.concat newline (List.map (fun '(w, p) => "    " ++ show w ++ if (p : bool) then "" else " (not propagated)")
                                             (List.combine s.(ws_writes) s.(ws_has_propagated)))
      }.
    Close Scope string_scope.

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
            (show i.(ins_id) ++ ":[" ++ show i.(ins_loc) ++ "] ")
              ++ ("'" ++ show i.(ins_ast) ++ "' " ++ (if i.(ins_finished) then "(finished)"
                                                      else "(in-flight)") ++ newline)
              ++ match i.(ins_reg_reads) with
                 | [] => ""
                 | _ => "  reg reads: " ++ show i.(ins_reg_reads) ++ newline
                 end
              ++ match i.(ins_reg_writes) with
                 | [] => ""
                 | _ => "  reg writes: " ++ show i.(ins_reg_writes) ++ newline
                 end
              ++ match i.(ins_mem_reads) with
                 | Some rs =>
                   ("  mem reads: " ++ newline)
                     ++ show rs ++ newline
                 | None => ""
                 end
              ++ match i.(ins_mem_writes) with
                 | Some ws =>
                   ("  mem writes: " ++ newline)
                     ++ show ws ++ newline
                 | None => ""
                 end
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

    Definition ins_tree : Type := tree decoded_instruction_state
                                       (tree (instruction_id * mem_loc) unit).
    (* the additional [bool] in [restart_ins_tree] indicates which instructions
       should be restarted *)
    Definition restart_ins_tree : Type := tree (bool * decoded_instruction_state)
                                               (tree (instruction_id * mem_loc) unit).

    Record _state :=
      mk_state { id : thread_id;
                 next_iid : instruction_id;
                 instruction_tree : ins_tree }.
    (* Workaround: parameter can't be instantiated by an inductive type *)
    Definition state := _state.

    #[global] Instance eta_state : Settable _ :=
      settable! mk_state <id; next_iid; instruction_tree>.

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
            ("Instruction tree: " ++ newline)
              ++ "  " ++ (show_dec_tree s.(instruction_tree)) ++ newline
              ++ "Instructions:" ++ newline
              ++ String.concat "" (List.map show_ins (tree_to_list_preorder s.(instruction_tree)))
      }.
    Close Scope string_scope.
  End State.
End Base.

(******************************************************************************)

Module Type ArcThreadSig.
  Declare Module Arc : ArcSig.
  Module Base := Base Arc.
  Export Base.

  Parameter sat_mem_read_restarts : state -> (mem_reads_from + (list mem_slc))
                                    -> list ins_tree
                                    -> list restart_ins_tree.

  Parameter propagate_write_restarts : state -> decoded_instruction_state -> mem_write
                                       -> list ins_tree
                                       -> list restart_ins_tree.

  Parameter  mem_read_request_cand : list decoded_instruction_state
                                     -> decoded_instruction_state -> bool.

  Parameter commit_store_cand : state -> list decoded_instruction_state
                                -> decoded_instruction_state -> bool.

  Parameter propagate_write_cand : state -> list decoded_instruction_state
                                   -> decoded_instruction_state -> mem_write -> bool.

  Parameter finish_cand : state -> list decoded_instruction_state
                          -> decoded_instruction_state -> bool.

  Parameter possible_write_forwarding : state -> list decoded_instruction_state
                                        -> decoded_instruction_state -> list mem_slc
                                        -> option (mem_reads_from * list mem_slc).
End ArcThreadSig.

Require SimpleA64InsSem.

Module SimpleArmv8A : ArcThreadSig with Module Arc := SimpleA64InsSem.Armv8A.
  Module Arc := SimpleA64InsSem.Armv8A.
  Module Base := Base Arc.
  Export Base.

  Open Scope bool_scope.

  Section InstructionKind.
    Variable a : ast.

    Definition is_strong_memory_barrier : bool :=
      match a with
      | DMB MBReqDomain_FullSystem MBReqTypes_All => true
      | _ => false
      end.
    Definition is_ld_barrier : bool :=
      match a with
      | DMB MBReqDomain_FullSystem MBReqTypes_Reads => true
      | _ => false
      end.
    Definition is_st_barrier : bool :=
      match a with
      | DMB MBReqDomain_FullSystem MBReqTypes_Writes => true
      | _ => false
      end.
    Definition is_memory_barrier : bool :=
      match a with
      | DMB MBReqDomain_FullSystem _ => true
      | _ => false
      end.
    Definition is_instruction_barrier : bool := (* FIXME: *) let a := a in false.

    Definition is_load : bool :=
      match a with
      | Load _ _ _ => true
      | _ => false
      end.
    Definition is_load_acquire : bool := (* FIXME: *) let a := a in false.
    Definition is_load_exclusive : bool := (* FIXME: *) let a := a in false.

    Definition is_store : bool :=
      match a with
      | Store _ _ _ => true
      | _ => false
      end.
    Definition is_store_release : bool := (* FIXME: *) let a := a in false.
    Definition is_store_exclusive : bool := (* FIXME: *) let a := a in false.

    Definition is_load_atomic : bool := (* FIXME: *) let a := a in false.
    Definition is_store_atomic : bool := (* FIXME: *) let a := a in false.
    Definition is_rmw : bool := (* FIXME: *) let a := a in false.
  End InstructionKind.

  (** Instruction instance predicates *)
  Section InstructionKindState.
    Variable ins : decoded_instruction_state.

    (* A failed store-conditional/exclusive is not considered a memory access after it is finished *)

    Definition atomic_store_determined_to_fail : bool :=
      (* FIXME: *)
      (* ins.successful_atomic_store = Just false. *)
      let ins := ins in false.

    (* let atomic_store_determined_to_succeed (i : instruction_instance 'i) : bool =  *)
    (*   i.successful_atomic_store = Just true *)

    Definition is_viable_store : bool :=
      is_store ins.(ins_ast) &&
      negb (atomic_store_determined_to_fail && ins.(ins_finished)).

    Definition is_viable_memory_access : bool :=
      is_load ins.(ins_ast) || is_viable_store.

    Definition is_cond_branch : bool :=
      (* FIXME: *)
      (* Set.size i.nias > 1 *)
      let ins := ins in false.

    Definition is_indirect_branch : bool :=
      (* FIXME: *)
      (* exists (nia IN i.nias). nia = NIA_indirect_address *)
      let ins := ins in false.

    Definition write_initiated : bool := isTrue (ins.(ins_mem_writes) <> None).

    (* let write_instantiated inst =  *)
    (*   write_initiated inst &&  *)
    (*   List.null inst.subwrites.sw_potential_write_addresses *)
    (* let write_committed inst = inst.subwrites.sw_committed *)

    (* let all_read_writes_have_their_values inst =  *)
    (*   forall ((_, wss) MEM inst.subreads.sr_writes_read_from) ((w,_) MEM wss). *)
    (*   w.w_value <> Nothing *)

    Definition propagated_writes writes :=
      List.map snd (List.filter fst (List.combine writes.(ws_has_propagated)
                                                           writes.(ws_writes))).

    Definition unpropagated_writes writes :=
      List.map snd (List.filter fst (List.combine (List.map negb writes.(ws_has_propagated))
                                                  writes.(ws_writes))).

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
      is_load ins.(ins_ast) ---> read_initiated.

    Definition all_writes_are_calculated : bool :=
      is_viable_store ---> write_initiated.

    (* return true iff the sail code has already generated all the memory-read/write *)
    (*    events (except AArch64 write-mem-value, i.e., E_write_memv) for the *)
    (*    instruction. This guarantees that any memory read/write footprint of the *)
    (*    instruction is recorded in the instruction_instance state. *)
    Definition all_writes_reads_are_calculated : bool :=
      (* for efficiency, first check if 'inst' is unfinished *)
      ins.(ins_finished)
      || (all_reads_are_calculated && all_writes_are_calculated).

    Definition is_entirely_satisfied_load : bool :=
      all_reads_are_calculated
      && read_completed.

    Definition finished_load_part : bool :=
      ins.(ins_finished). (* || ins.rmw_finished_load_snapshot <> Nothing *)
    End InstructionKindState.


  Section InstructionPrefixPreds.
    Fixpoint undetermined_reg_data_flow_sources_helper
             (pref : list decoded_instruction_state)
             (iid : instruction_id)
             (ind : nat)
      : list instruction_id :=
      match pref with
      | [] => []  (* if [iid] is not in [pref] then it is an old
                    instruction, and therefore must be finised. *)
      | ins::pref =>
        if decide (ins.(ins_id) = iid) then
          if ins.(ins_finished) then [] else
            (* NOTE: we assume rmw instructions write to registers only in the load part *)
            (* if i.rmw_finished_load_snapshot <> Nothing then {} else *)
            match List.nth_error ins.(ins_reg_writes) ind with
            | Some rws =>
              let res :=
                  List.concat
                    (List.map (fun '(iid, ind) => undetermined_reg_data_flow_sources_helper pref iid ind)
                              rws.(rws_reg_data_flow)) in
              if rws.(rws_mem_data_flow) then iid::res
              else res
            | None => [iid] (* the register write disappeared, i.e. [iid] was
                              restarted, yet the register dependent instruction
                              that initiated this check was not restarted. That
                              can happen when the register write is
                              deterministic (e.g. the status register of AArch64
                              STXR). This means we can return [nil] here, but it
                              feels unsafe. Since this scenario involves
                              restarts it does not really matter, so I do the
                              safer thing which is to return [[iid]]. *)
            end
        else
          undetermined_reg_data_flow_sources_helper pref iid ind
      end.

    (* FIXME: the result has duplicates; use set instead of list? *)
    (* LEM: machineDefThreadSubsystemUtils.lem: undetermined_reg_writes_read_from *)
    Definition undetermined_reg_data_flow_sources
               (pref : list decoded_instruction_state)
               (rrss : list reg_read_state)
      : list instruction_id :=
      List.concat
        (List.map (fun rrs =>
                     List.concat
                       (List.map (fun '(iid, ind, _) =>
                                    undetermined_reg_data_flow_sources_helper pref iid ind)
                                 rrs.(rrs_reads_from)))
                  rrss).


    (* check if the instructions feeding register reads are finished. *)
    (* If an instruction is not finished, recursively check the register write's *)
    (* dependencies *)
    Definition fully_determined_reg_reads
               (pref : list decoded_instruction_state)
               (rrss : list reg_read_state)
      : bool:=
      match undetermined_reg_data_flow_sources pref rrss with
      | [] => true
      | _::_ => false
      end.


    (* [true] iff the value read from registers that feed directly into a memory *)
    (* access address of [ins] cannot change, and the pseudocode has made *)
    (* enough steps to make the address visible *)
    Definition fully_determined_address
               (pref : list decoded_instruction_state)
               (ins : decoded_instruction_state)
      (* po: head is new. ASSUME: super set of the po-prefix of [ins] *)
      : bool :=
      (* for efficiency, first check if [ins] is finished or not a memory access *)
      ins.(ins_finished) || negb (is_viable_memory_access ins)

      (* the value read from registers that feed directly into a memory *)
      (* access address of [ins] cannot change *)
      || (fully_determined_reg_reads pref (List.filter rrs_feeding_addr ins.(ins_reg_reads)) &&

         (* the pseudocode has made enough steps to make the address visible *)
         (is_viable_store ins ---> write_initiated ins) &&
         (is_load ins.(ins_ast) ---> read_initiated ins)).


    Definition preceding_memory_accesses_have_fully_determined_address
               (pref : list decoded_instruction_state)
      : bool :=
      list_forall_suffixb (fun pref => match pref with
                                    | [] => true
                                    | ins::pref => fully_determined_address pref ins
                                    end)
                          pref.

    Definition preceding_reads_writes_are_calculated
               (pref : list decoded_instruction_state)
      : bool :=
      forallb all_writes_reads_are_calculated pref.

    Definition dataflow_committed
               (pref : list decoded_instruction_state)
               (ins : decoded_instruction_state)
      : bool :=
      fully_determined_reg_reads pref ins.(ins_reg_reads).


    Definition controlflow_committed
               (pref : list decoded_instruction_state)
      : bool :=
      (forallb (fun prev_ins =>
                  is_cond_branch prev_ins ---> prev_ins.(ins_finished))
               pref) &&
      (forallb (fun prev_ins =>
                  is_indirect_branch prev_ins ---> prev_ins.(ins_finished))
               pref).
  End InstructionPrefixPreds.

  Section Exclusives.
    Definition paired_load_atomic
               (* [full_pref] should include both the active instructions and
                  the old ones. *)
               (full_pref : list decoded_instruction_state)
               (ins : decoded_instruction_state)
    : option decoded_instruction_state :=
      if is_rmw ins.(ins_ast) then Some ins
      else
        let is_atomic ins := (is_load_atomic ins.(ins_ast) || is_store_atomic ins.(ins_ast))
                             && negb (is_rmw ins.(ins_ast)) in
        match List.find is_atomic full_pref with
        | Some atomic_ins =>
          if is_load_atomic atomic_ins.(ins_ast) then Some atomic_ins
          else None
        | None => None
        end.

    (* Fixpoint paired_atomic_stores_helper *)
    (*          (T its: instruction_tree 'i) *)
    (*   : list (instruction_instance 'i) := *)
    (*   its >>= fun (i, it) -> *)
    (*             if is_atomic_load (ik i) && not (is_memory_rmw (ik i)) then [] *)
    (*             else if is_atomic_store (ik i) && not (is_memory_rmw (ik i)) then [i] *)
    (*                  else paired_atomic_stores_helper it. *)

    (* Fixpoint paired_atomic_stores (i: instruction_instance 'i) (it: instruction_tree 'i) *)
    (*     : list (instruction_instance 'i) := *)
    (*   if is_memory_rmw (ik i) then [i] *)
    (*   else paired_atomic_stores_helper it *)

  End Exclusives.

  (* LEM: machineDefThreadSubsystem.lem: pop_memory_read_request_cand *)
  Definition mem_read_request_cand (pref : list decoded_instruction_state)
             (ins : decoded_instruction_state) : bool :=
    (* NOTE: we don't check that po-preceding instructions to the same address
       are finished. See also private comment THREAD1 *)
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

    (* load-acquire/store-release: A store-release and a po-succeeding
       load-acquire are observed in program order *)
    (is_load_acquire ins.(ins_ast)
     ---> forallb (fun prev_ins =>
                 is_store_release prev_ins.(ins_ast)
                 ---> prev_ins.(ins_finished))
              pref) &&

    (* All po-preceding load-acquires must issue their requests before the read
         request. Also see private note THREAD3 *)
    (forallb (fun prev_ins =>
               is_load_acquire prev_ins.(ins_ast)
               ---> (finished_load_part prev_ins ||
                  is_entirely_satisfied_load prev_ins))
             pref).


  (* LEM: machineDefThreadSubsystem.lem: pop_commit_store_cand *)
  Definition commit_store_cand
             (st : state)
             (pref : list decoded_instruction_state)
             (ins : decoded_instruction_state) : bool :=
    (* all po-preceding memory access locations are fully determined *)
    preceding_memory_accesses_have_fully_determined_address pref &&
    (* to simplify the rest of the checks we also require that iprev has made
       enough steps to guarantee all the read/write requests are recorded in the
       instruction_instance state. *)
    preceding_reads_writes_are_calculated pref &&

    dataflow_committed pref ins &&
    controlflow_committed pref &&

    (forallb (fun prev_ins =>
                (is_strong_memory_barrier prev_ins.(ins_ast) ||
                 is_instruction_barrier prev_ins.(ins_ast))
                  ---> prev_ins.(ins_finished))
             pref) &&

    (* barrier.st/ld *)
    (forallb (fun prev_ins =>
                (is_st_barrier prev_ins.(ins_ast) ---> prev_ins.(ins_finished)) &&
                (is_ld_barrier prev_ins.(ins_ast) ---> prev_ins.(ins_finished)))
             pref) &&

    (* load.acquire/store.release: *)
    (* TODO: the following might be too strong, a previous read only
       needs to be issued and non-restartable. *)
    ((is_store_release ins.(ins_ast))
       ---> (forallb (fun prev_ins =>
                        (is_viable_memory_access prev_ins)
                          ---> prev_ins.(ins_finished))
                     pref)) &&

    (forallb (fun prev_ins =>
                (is_load_acquire prev_ins.(ins_ast))
                  ---> finished_load_part prev_ins)
             pref) &&

  (* load/store-exclusive *)
  ((is_store_exclusive ins.(ins_ast))
     --->
     (* FIXME: [pref] below should be the complete prefix (including old
        instructions). *)
     match paired_load_atomic pref ins with
     (* "can't find the paired load of a successful atomic store" *)
     (* failed store-exclusive uses a different _cand function *)
     | None => false
     | Some load_ins =>
       finished_load_part load_ins &&
       match load_ins.(ins_mem_reads) with
       | None => false
       | Some reads =>
         forallb (fun rf =>
                    forallb (fun '((tid, iid, MemWriteID wid), _) =>
                               (isTrue (tid = st.(id)))
                                 --->
                                 (forallb (fun prev_ins =>
                                             (isTrue (prev_ins.(ins_id) = iid))
                                               --->
                                               match prev_ins.(ins_mem_writes) with
                                               | None => false
                                               | Some writes =>
                                                 match List.nth_error writes.(ws_has_propagated) wid with
                                                 | None => false
                                                 | Some b => b
                                                 end
                                               end)
                                          pref))
                            rf)
                 reads.(rs_reads_from)
       end
     end).




  Definition all_po_preceding_overlapping_reads_issued_and_non_restartable
             (pref : list decoded_instruction_state)
             (write : mem_write)
             (might_be_restarted : list instruction_id)
    : bool :=
    forallb (fun prev_ins =>
               match prev_ins.(ins_mem_reads) with
               | None => true
               | Some reads =>
                 forallb (fun '(r, uslc) =>
                            ((non_empty_intersection write.(write_footprint) r.(read_footprint))
                               ---> (isTrue (uslc = []))
                             (* and [prev_ins] can't be restarted *)
                             && isTrue (~ In prev_ins.(ins_id) might_be_restarted)))
                         (List.combine reads.(rs_reads) reads.(rs_unsat_slcs))
               end)
            pref.

  Definition all_po_preceding_overlapping_unpropagated_writes_covered
             (prev_unpropagated_writes : list mem_write) (write : mem_write)
    : bool :=
    forallb (fun prev_write =>
               (non_empty_intersection write.(write_footprint) prev_write.(write_footprint))
                 ---> contained prev_write.(write_footprint) write.(write_footprint))
            prev_unpropagated_writes.

  Definition no_po_preceding_overlapping_unpropagated_writes
             (prev_unpropagated_writes : list mem_write) (write : mem_write)
    : bool :=
    forallb (fun prev_write =>
               negb (non_empty_intersection write.(write_footprint)
                                                    prev_write.(write_footprint)))
        prev_unpropagated_writes.

  Definition write_allowed_to_be_subsumed (ins : decoded_instruction_state)
    : bool :=
    (* FIXME:
       params.thread_allow_write_subsumption && *)
    false &&
    negb (is_store_release ins.(ins_ast)) &&
    negb (is_store_atomic ins.(ins_ast)).

  Section Restart.
    (* LEM: machineDefThreadSubsystem.lem: dependent_suffix_to_restart [true]
       iff [ins] should be restarted, given that the preceding instructions in
       [pref] that are tagged with [true] have been restarted. *)
    Definition restart_successor
               (s : state)
               (pref : list (bool * decoded_instruction_state))
               (ins : decoded_instruction_state)
    : bool :=
      let restarted_iids := List.map (fun '(_, i) => i.(ins_id)) (List.filter fst pref) in
      (* register data flow source restarted *)
      existsb (fun iid => isTrue (In iid restarted_iids))
              (undetermined_reg_data_flow_sources (List.map snd pref)
                                                  ins.(ins_reg_reads))
      (* mem read satisifed by a restarted write forward *)
      || match ins.(ins_mem_reads) with
        | None => false
        | Some reads =>
          existsb (fun '((tid, iid, _), _) =>
                     isTrue (tid = s.(id) /\ In iid restarted_iids))
                  (List.concat reads.(rs_reads_from))
        end
      (* load succeeding a restarted load-acquire *)
      || (is_load ins.(ins_ast)
         && existsb (fun '(restarted, prev_ins) =>
                       is_load_acquire prev_ins.(ins_ast)
                       && restarted
                       && negb (finished_load_part prev_ins))
                    pref).


    (* see if there is a pair of distinct writes in [rf] and [rf'] whose slices
       footprint-intersect and where the second does not come from an
       instruction in [prev_iids] *)
    Definition reads_from_nonforwarding_different_overlapping_write
               (s : state)
               (rf: mem_reads_from)
               (rf': mem_reads_from)
               (prev_iids: list instruction_id)
    : bool :=
      existsb (fun '((tid', iid', wid') as id', (slc', _)) =>
                 (* non-forwarding *)
                 isTrue (tid' <> s.(id) \/ ~ In iid' prev_iids)
                 && existsb (fun '(id, (slc, _)) =>
                               (* different *)
                               isTrue (id <> id')
                               (* overlapping *)
                               && non_empty_intersection slc slc')
                            rf)
              rf'.

    Definition sat_mem_read_restarts
               (s : state)
               (ss : mem_reads_from
                     + (list mem_slc))
               (subts : list ins_tree)
      :  list restart_ins_tree :=
      List.map
        (tree_map_in_context
           (fun pref suc_ins _ =>
              let restart_root :=
                  match suc_ins.(ins_mem_reads) with
                  | None => false
                  | Some reads =>
                    match ss with
                    | inl rf =>
                      let pref_iids := List.map (fun '(_, i) => i.(ins_id)) pref in
                      existsb (fun rf' =>
                                 reads_from_nonforwarding_different_overlapping_write
                                   s rf rf' pref_iids)
                              reads.(rs_reads_from)
                    | inr rs =>
                      existsb (fun r' => existsb (non_empty_intersection r'.(read_footprint)) rs)
                              reads.(rs_reads)
                    end
                  end in
              (restart_root || restart_successor s pref suc_ins, suc_ins))
           (fun _ l => l) [])
        subts.

    Definition propagate_write_restarts
               (s : state)
               (ins : decoded_instruction_state)
               (write : mem_write)
               (subts : list ins_tree)
      :  list restart_ins_tree :=
      let wslcs := [((s.(id), ins.(ins_id), write.(write_id)),
                     (write.(write_footprint), write.(write_val)))] in
      List.map
        (tree_map_in_context
           (fun pref suc_ins _ =>
              let restart_root :=
                  match suc_ins.(ins_mem_reads) with
                  | None => false
                  | Some reads =>
                    let pref_iids := List.map (fun '(_, i) => i.(ins_id)) pref in
                    (* Restart loads that have been satisfied by writes that are
                    co-before [write] *)
                    reads_from_nonforwarding_different_overlapping_write
                      s wslcs (List.concat reads.(rs_reads_from)) pref_iids
                    (* Restart loads that have a read that was partially satisfied
                    by forwarding [write], and is not yet fully satisfied. This
                    prevents single-copy atomicity violations such as
                    CO-MIXED-20cc.
                    The Lem model doesn't do this restart, instead it prevents
                    [write] from being propagated. *)
                    || existsb (fun '(uslcs, rf) =>
                                 isTrue (uslcs <> [])
                                 && existsb (fun '((tid, iid, wid), _) =>
                                               isTrue (tid = s.(id) /\ iid = ins.(ins_id)
                                                       /\ wid = write.(write_id)))
                                            rf)
                              (List.combine reads.(rs_unsat_slcs) reads.(rs_reads_from))
                  end in
              (restart_root || restart_successor s pref suc_ins, suc_ins))
           (fun _ l => l) [])
        subts.

    Definition commit_store_exc_fail_restarts
               (s : state)
               (ins : decoded_instruction_state)
               (subts : list ins_tree)
      :  list restart_ins_tree :=
      List.map
        (tree_map_in_context
           (fun pref suc_ins _ => (restart_successor s pref suc_ins, suc_ins))
           (fun _ l => l) [(true, ins)])
        subts.

    Definition store_action_might_restart
               (s : state)
               (ins : decoded_instruction_state)
               (subt : ins_tree)
               (might_restart : NatSet.t)
      : NatSet.t :=
      if negb (is_viable_store ins) || ins.(ins_finished) then might_restart
      else match ins.(ins_mem_writes) with
           | None => might_restart
           | Some writes =>
             let write_restarts (success : bool) :=
                 if success then
                   List.fold_left
                     (fun might_restart write =>
                        List.fold_left (fun might_restart subt =>
                                          List.fold_left
                                            (fun might_restart n =>
                                               match n with
                                               | inl (true, i) =>
                                                 let '(InstructionID iid) := i.(ins_id) in
                                                 NatSet.add iid might_restart
                                               | _ => might_restart
                                               end)
                                            (tree_to_list_preorder subt)
                                            might_restart)
                                       (propagate_write_restarts s ins write [subt])
                                       might_restart)
                     (unpropagated_writes writes)
                     might_restart
                 else
                   List.fold_left (fun might_restart subt =>
                                     List.fold_left
                                       (fun might_restart n =>
                                          match n with
                                          | inl (true, i) =>
                                            let '(InstructionID iid) := i.(ins_id) in
                                            NatSet.add iid might_restart
                                          | _ => might_restart
                                          end)
                                       (tree_to_list_preorder subt)
                                       might_restart)
                                  (commit_store_exc_fail_restarts s ins [subt])
                                  might_restart in
             if is_store_atomic ins.(ins_ast) then
               (* FIXME:
               match instruction.successful_atomic_store with
               (* [None] means success undetermined, [Some true] means determined to succeed*)
               | None -> NatSet.union (write_restarts true)
                                     (write_restarts false)
               | Some b -> write_restarts b
               end *)
               write_restarts true
             else
               write_restarts true
           end.

    Definition load_action_might_restart
               (s : state)
               (ins : decoded_instruction_state)
               (subt : ins_tree)
               (might_restart : NatSet.t)
      : NatSet.t :=
      if ins.(ins_finished) then might_restart
      else match ins.(ins_mem_reads) with
           | None => might_restart
           | Some reads =>
             let '(InstructionID iid) := ins.(ins_id) in
             let rslcss :=
                 if NatSet.mem iid might_restart then
                   (* because the load migh be restarted, we have to assume it will
                      be, and then resatisfied, hence the complete slice below. *)
                   [[reads.(rs_footprint)]]
                 else
                   reads.(rs_unsat_slcs) in
             (* The folds below can be replaced with maps and unions. *)
             List.fold_left
               (fun might_restart slcs =>
                  List.fold_left (fun might_restart subt =>
                                    List.fold_left
                                      (fun might_restart n =>
                                         match n with
                                         | inl (true, i) =>
                                           let '(InstructionID iid) := i.(ins_id) in
                                           NatSet.add iid might_restart
                                         | _ => might_restart
                                         end)
                                      (tree_to_list_preorder subt)
                                      might_restart)
                                 (sat_mem_read_restarts s (inr slcs) [subt])
                                 might_restart)
               rslcss might_restart
           end.

    (* Return the set of instructions in [pref] that might be restarted in the
       future.
       ASSUME: all memory access instructions in [pref] have calculated their
       memory address and all the instructions feeding these calculations are
       propagated (i.e. addresses are known and cannot change). *)
    Definition might_be_restarted
               (s :  state)
               (pref: list decoded_instruction_state)
      : list instruction_id :=
      let '(_, pref_trees) := List.fold_left (fun '(t, ts) i => (TNode i [t], (i, t)::ts))
                                             pref ((TLeaf (TLeaf tt)), []) in
      let might_restart :=
          List.fold_left
            (fun might_restart '(ins, subt) =>
               NatSet.union
                 (store_action_might_restart s ins subt might_restart)
                 (load_action_might_restart s ins subt might_restart))
            pref_trees
            NatSet.empty in
      List.map InstructionID (NatSet.elements might_restart).
  End Restart.

  (* LEM: machineDefThreadSubsystem.lem: propagate_write_cand
     (which calls pop_write_co_check) *)
  Definition propagate_write_cand
             (s : state)
             (pref : list decoded_instruction_state)
             (ins : decoded_instruction_state)
             (write : mem_write)
    : bool :=
    let might_be_restarted := might_be_restarted s pref in

    (* Guarantee RW-coherence *)
    all_po_preceding_overlapping_reads_issued_and_non_restartable
      pref write might_be_restarted

    (* Guarantee WW-coherence *)
    && forallb (fun prev_ins =>
                  if atomic_store_determined_to_fail prev_ins then
                    true
                  else
                    match prev_ins.(ins_mem_writes) with
                    | None => true
                    | Some prev_writes =>
                      let prev_unpropagated_writes := unpropagated_writes prev_writes in
                      (* FIXME: (if we want to support write-subsumption)
                         if pop_write_allowed_to_be_subsumed params iprev then
                           pop_all_po_preceding_overlapping_unpropagated_writes_covered
                             prev_unpropagated_writes write
                         else *)
                      no_po_preceding_overlapping_unpropagated_writes
                        prev_unpropagated_writes write
                    end)
               pref.

  Definition is_fixed_store pref ins : bool :=
    is_store ins.(ins_ast)
    && dataflow_committed pref ins.

  Fixpoint finish_mem_reads_co_check_helper
             (s : state)
             (pref : list decoded_instruction_state)
             (might_be_restarted : list instruction_id)
             (rf : mem_reads_from)
    : bool:=
    match pref with
    | [] => true
    | prev_ins::pref =>
      (* memory address of 'prev_ins' is fully determined *)
      fully_determined_address pref prev_ins

      (* to simplify the rest of the checks we also require that 'prev_ins' has
         made enough steps to guarantee all the read/write requests are
         recorded in the instruction_instance state. *)
      && all_writes_reads_are_calculated prev_ins

      && match prev_ins.(ins_mem_reads) with
         | Some prev_reads =>
           (* Overlapping reads must be satisfied and non-restartable. *)
           finished_load_part prev_ins (* optimisation (but maybe necessary for AMOs?) *)
           || (forallb (fun '(_, (slc, _)) =>
                         forallb (fun '(r, uslcs) =>
                                    (non_empty_intersection r.(read_footprint) slc)
                                      --->
                                      (isTrue (~ (In prev_ins.(ins_id) might_be_restarted))
                                       && forallb (non_empty_intersection slc) uslcs))
                                 (List.combine prev_reads.(rs_reads) prev_reads.(rs_unsat_slcs)))
                      rf)
         | None => true
         end

      && match prev_ins.(ins_mem_writes) with
         | Some prev_writes =>
           forallb (fun write =>
                      forallb (fun '(_, (slc, _)) =>
                                 negb (non_empty_intersection slc write.(write_footprint)))
                              rf)
                   (unpropagated_writes prev_writes)
         | None => true
         end

      && (
        (* filter out slices that were forwarded from fixed writes *)
        let rf :=
            if is_fixed_store pref prev_ins then
              List.filter (fun '((tid, iid, _), _) =>
                             isTrue (tid <> s.(id) \/ iid <> prev_ins.(ins_id)))
                          rf
            else rf
        in

        (* FIXME: I think the following is an optimisation, but not necessary
        let rf = parts_of_read_rf_not_overwritten_by_write
                               rf read_request prev_ins in *)

        if decide (rf = []) then true
        else finish_mem_reads_co_check_helper s pref might_be_restarted rf)
    end.


  (* pop might-access-same-address (for loads) The closest po-previous write to
     the same address must be propagated and all memory accesses in-between must
     have a fully determined addresses, except if the closest po-previous write
     is a write that was forwarded to the load, then it does not have to be
     propagated, just "fixed" (i.e. instructions feeding ALL its registers are
     determined). *)
  Definition finish_mem_reads_co_check
             (s : state)
             (pref : list decoded_instruction_state)
             (reads : mem_reads_state)
    : bool :=
    (* any observable behaviour that depends on the load being finished ([R];
       ctrl; [W] or [R]; ctrl+isb; [R] or [Raq]; po; [W] , etc) also depends on
       the po-prefix having fully determined addresses, hence it is ok for
       might_be_restarted to over-approximate if the po-prefix does not have
       fully determined addresses *)
    let might_be_restarted :=
        (* to simplify the rest of the checks we also require that iprev has
           made enough steps to guarantee all the read/write requests are
           recorded in the instruction state. *)
        if preceding_memory_accesses_have_fully_determined_address pref
           && preceding_reads_writes_are_calculated pref then
          might_be_restarted s pref
        else List.map ins_id (List.filter (fun i => negb i.(ins_finished)) pref) in

    forallb (finish_mem_reads_co_check_helper s pref might_be_restarted)
            reads.(rs_reads_from).

  Definition finish_cand (s : state) (pref : list decoded_instruction_state)
             (ins : decoded_instruction_state)
    : bool :=
    dataflow_committed pref ins
    && controlflow_committed pref

    (** Load *)
    && match ins.(ins_mem_reads) with
       | Some reads =>
         (forallb (fun prev_ins =>
                     (is_load_acquire prev_ins.(ins_ast))
                       ---> finished_load_part prev_ins)
                  pref)
         && finish_mem_reads_co_check s pref reads
       | None => true
       end

    (** Barrier *)
    (* Commit order between barriers *)
    && ((is_strong_memory_barrier ins.(ins_ast))
          ---> (forallb (fun prev_ins =>
                          (is_memory_barrier prev_ins.(ins_ast)
                           || is_instruction_barrier prev_ins.(ins_ast))
                            ---> prev_ins.(ins_finished))
                        pref))
    && (forallb (fun prev_ins =>
                   (is_strong_memory_barrier prev_ins.(ins_ast))
                     ---> prev_ins.(ins_finished))
                pref)

    && ((is_strong_memory_barrier ins.(ins_ast))
          ---> (forallb (fun prev_ins =>
                           (is_viable_memory_access prev_ins)
                             ---> prev_ins.(ins_finished))
                        pref))

    && ((is_instruction_barrier ins.(ins_ast))
          ---> preceding_memory_accesses_have_fully_determined_address pref)

    && ((is_ld_barrier ins.(ins_ast))
          ---> (forallb (fun prev_ins =>
                           (is_load prev_ins.(ins_ast))
                             ---> finished_load_part prev_ins)
                        pref))

    && ((is_st_barrier ins.(ins_ast))
          ---> (forallb (fun prev_ins =>
                           (is_store prev_ins.(ins_ast))
                             ---> prev_ins.(ins_finished))
                        pref)).

  Existing Instance slice_prod_r.

  Definition possible_write_forwarding
             (s : state)
             (pref : list decoded_instruction_state)
             (ins : decoded_instruction_state)
             (unsat_slcs : list mem_slc)
    : option (mem_reads_from * list mem_slc) :=
    (* Collect all the write slices that have been observed in [pref]. Some of
       those writes will be forwarded, some will "block" forwarding. See private
       comments THREAD4, THREAD5, THREAD6. *)
    let writes :=
        List.concat
          (List.map (fun prev_ins =>
                       match prev_ins.(ins_mem_writes) with
                       | Some writes =>
                         (* FIXME: [writes] might have an empty [ws_writes],
                            when the address has been instantiated, but the
                            value has not. I'm not sure if we need to add
                            [writes.ws_footprint] or not. *)
                         List.map (fun '(w, p) =>
                                     let can_be_forwarded :=
                                         negb p
                                         && negb (is_load_acquire ins.(ins_ast)
                                                  && is_store_exclusive prev_ins.(ins_ast)) in
                                     ((can_be_forwarded, s.(id), prev_ins.(ins_id), w.(write_id)),
                                      (w.(write_footprint), w.(write_val))))
                                  (List.combine writes.(ws_writes) writes.(ws_has_propagated))
                       | None => []
                       end
                         ++ match prev_ins.(ins_mem_reads) with
                            | Some reads =>
                              List.map (fun '((tid, iid, wid), slc) => ((false, tid, iid, wid), slc))
                                       (List.concat reads.(rs_reads_from))
                            | None => []
                            end)
                    pref) in
    match reads_from_slcs writes unsat_slcs [] with
    | Some (rf, _) =>
      (* Remove from [rf] writes that are not for forwarding. *)
      let rf :=
          List.map (fun '((_, tid, iid, wid), slc) => ((tid, iid, wid), slc))
                   (List.filter (fun '((can_be_forwarded, _, _, _), _) =>
                                   can_be_forwarded)
                                rf) in
      (* The following call to [reads_from_slcs] returns the same [rf]. We
         call it to compute the unsat slices. *)
      reads_from_slcs rf unsat_slcs []
    | None => None (* unreachable *)
    end.

End SimpleArmv8A.

(******************************************************************************)

Module Make (Arc : ArcSig) (ArcThread : ArcThreadSig with Module Arc := Arc) : ThreadSig Arc.
  Import ArcThread.

  Definition state := state.
  Definition showable_state := showable_state.
  Definition E := E.
  Definition showable_E := showable_E.
  Definition is_eager_event {A T} := @is_eager_event A T.
  Definition denote {F} := @denote F.

  Definition initial_state '(tid : thread_id)
             '((InstructionID iid) : instruction_id) (loc : mem_loc)
    : state :=
    {| id := tid;
       next_iid := InstructionID (iid + 1);
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
        let wslcs :=
            (* Using ListMonad to do filter-map *)
            '(i, w) <- List.combine (List.seq 0 (List.length ins.(ins_reg_writes)))
                                   ins.(ins_reg_writes)
            ;; if decide (w.(rws_slc_val).(rsv_slc).(rs_reg) = r) then
                 ret ((ins.(ins_id), i), w.(rws_slc_val))
               else nil in

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
               w (* FIXME: this shouldn't be reachable *)
           | None => w (* FIXME: this shouldn't be reachable *)
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

  Definition apply_restarts (subts : list restart_ins_tree)
    : (list instruction_id * list ins_tree) :=
    let '(restarted_iids, subts) :=
        List.split
          (List.map
             (fun subt =>
                let restarted_iids :=
                    n <- tree_to_list_preorder subt
                    ;; match n with
                       | inl (true, i) => [i.(ins_id)]
                       | _ => []
                       end in
                let subt :=
                    tree_map (fun '((restart, i) : bool * _) =>
                                if restart then
                                  initial_decoded_instruction_state i.(ins_id) i.(ins_loc) i.(ins_ast)
                                else i)
                             (fun l => l) subt in
                (restarted_iids, subt))
             subts) in
    (List.concat restarted_iids, subts).

  Section Handle_instruction_instance.
    Variable iid : instruction_id.

    Context {F : Type -> Type}.
    Context `{storageE -< F}.
    Context `{stateE state -< F}.
    Context `{exceptE disabled -< F}.
    Context `{exceptE error -< F}.
    Context `{debugE -< F}.

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
      ;; guard (finish_cand s pref ins)
      (* FIXME: if the instruction is a branch, prune the instruction tree *)
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


    Definition try_sat_mem_load_op_forwarding '((MemReadID rid) : mem_read_id)
      : itree F (bool * list instruction_id) :=
      s <- get
      ;; '(pref, ins, subts) <- try_get_dec_instruction_state iid s
      ;; 'tt <- guard (ArcThread.mem_read_request_cand pref ins)
      ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                      "try_sat_mem_load_op_forwarding: no mem reads."
      ;; rr <- try_unwrap_option (List.nth_error rs.(rs_reads) rid)
                                "try_sat_mem_load_op_forwarding: missing read"
      ;; unsat_slcs <- try_unwrap_option (List.nth_error rs.(rs_unsat_slcs) rid)
                                        "try_sat_mem_load_op_forwarding: missing unsat slices."
      ;; rf_old <- try_unwrap_option (List.nth_error rs.(rs_reads_from) rid)
                                        "try_sat_mem_load_op_forwarding: missing rid."
      ;; '(rf_new, unsat_slcs) <- try_unwrap_option
                                   (possible_write_forwarding s pref ins unsat_slcs)
                                   "try_sat_mem_load_op_forwarding: unexpected None"
      ;; guard (isTrue (rf_new <> []))
      ;; let rs := (rs <| rs_unsat_slcs := list_replace_nth rid unsat_slcs
                                                            rs.(rs_unsat_slcs) |>)
                     <| rs_reads_from := list_replace_nth rid (rf_old ++ rf_new)
                                                          rs.(rs_reads_from) |> in
         let ins := ins <| ins_mem_reads := Some rs |> in
         let '(restarted_iids, subts) :=
             apply_restarts (sat_mem_read_restarts s (inl rf_new) subts) in
         let s := update_dec_instruction_state_and_subts iid ins subts s in
         'tt <- put s
      ;; ret (isTrue (unsat_slcs = []), restarted_iids).

    Definition try_sat_mem_load_op_from_storage '((MemReadID rid) : mem_read_id)
      : itree F (list instruction_id) :=
      s <- get
      ;; '(pref, ins, subts) <- try_get_dec_instruction_state iid s
      ;; 'tt <- guard (ArcThread.mem_read_request_cand pref ins)
      ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                      "try_sat_mem_load_op_from_storage: no mem reads."
      ;; unsat_slcs <- try_unwrap_option (List.nth_error rs.(rs_unsat_slcs) rid)
                                        "try_sat_mem_load_op_from_storage: missing rid."
      ;; rr <- try_unwrap_option (List.nth_error rs.(rs_reads) rid)
                                "try_sat_mem_load_op_from_storage: missing rid"
      ;; rf_forward <- try_unwrap_option (List.nth_error rs.(rs_reads_from) rid)
                                        "try_sat_mem_load_op_from_storage: missing rid."
      ;; rf_storage <- trigger (StERead rr unsat_slcs)
      ;; let rs := (rs <| rs_unsat_slcs := list_replace_nth rid [] rs.(rs_unsat_slcs) |>)
                     <| rs_reads_from := list_replace_nth rid (rf_forward ++ rf_storage)
                                                                                                                          rs.(rs_reads_from) |> in
         let ins := ins <| ins_mem_reads := Some rs |> in
         let '(restarted_iids, subts) :=
             apply_restarts (sat_mem_read_restarts s (inl rf_storage) subts) in
         let s := update_dec_instruction_state_and_subts iid ins subts s in
         'tt <- put s
      ;; ret restarted_iids.

    Definition try_complete_load_ops : itree F mem_slc_val :=
      s <- get
      ;; '(_, ins, _) <- try_get_dec_instruction_state iid s
      ;; rs <- try_unwrap_option ins.(ins_mem_reads)
                                      "try_complete_load_ops: no mem reads."
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
         let ws := (ws <| ws_writes := writes |>)
                     <| ws_has_propagated := List.map (fun _ => false) writes |>in
         let ins := ins <| ins_mem_writes := Some ws |> in
         let s := update_dec_instruction_state iid ins s in
         put s.

    Definition try_commit_store_instruction : itree F (list mem_write_id) :=
      s <- get
      ;; '(pref, ins, _) <- try_get_dec_instruction_state iid s
      ;; 'tt <- guard (commit_store_cand s pref ins)
      ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                      "try_commit_store_instruction: no mem writes"
      ;; let wids := List.map write_id ws.(ws_writes) in
         ret wids.

    Definition try_propagate_store_op '((MemWriteID wid) : mem_write_id)
      : itree F (list instruction_id) :=
      s <- get
      ;; '(pref, ins, subts) <- try_get_dec_instruction_state iid s
      ;; ws <- try_unwrap_option ins.(ins_mem_writes)
                                      "try_propagate_store_op: no mem writes"
      ;; w <- try_unwrap_option (List.nth_error ws.(ws_writes) wid)
                               "try_propagate_store_op: missing wid"
      ;; 'tt <- guard (propagate_write_cand s pref ins w)
      ;; 'tt <- trigger (StEWrite w)
      ;; let ws := ws <| ws_has_propagated := list_replace_nth wid true ws.(ws_has_propagated) |> in
         let ins := ins <| ins_mem_writes := Some ws |> in
         let '(restarted_iids, subts) :=
             apply_restarts (propagate_write_restarts s ins w subts) in
         let s := update_dec_instruction_state_and_subts iid ins subts s in
         'tt <- put s
      ;; ret restarted_iids.

    Definition try_complete_store_ops : itree F unit :=
      (* FIXME: is there anything we need to check here? *)
      let iid := iid in
      ret tt.

    (* TODO: We don't do anything here, the real checks are when the instruction
       is being finished. *)
    Definition handle_barrier : barE ~> itree F :=
      fun _ e =>
        match e with
        | BarEMem kind => ret tt
        end.

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
          (* Barrier events *)
          | ThEBarrier _ e => handle_barrier _ e
          end in
      'tt <- trigger (Debug ("handle_E: " ++ show e))
      ;; it.
End Make.
