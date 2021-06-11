From Coq Require Import
     Arith.PeanoNat
     NArith.NArith
     Lists.List
     Lists.ListSet
     Strings.String
     Morphisms
     Setoid
     RelationClasses .

Import ListNotations.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.ListMonad.
(*      Data.String *)
(*      Structures.Traversable *)
(*      Data.List. *)
(* Import ListMonad. *)

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
     Events.Nondeterminism
     Events.State.
Import Monads.
Import MonadNotation.
Import ITreeNotations.

(* The [sum1] types with automatic application of commutativity and
   associativity are prone to infinite instance resolution loops.
   This bounds the instance search depth: *)
Typeclasses eauto := 5.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import
        Types
        Utils.

Local Open Scope list.
Local Open Scope itree_scope.
Local Open Scope monad_scope.
Local Open Scope record_set.

Definition instruction_id_t := id_t.
Definition mem_read_id_t := id_t.
Definition mem_write_id_t := id_t.

Module Denote (Arc : ArcSig).
  Variant threadE : Type -> Type :=
  | ThEInsFetchAndDecode : threadE Arc.InsSem.ast
  | ThEInsNextLocs : threadE (list instruction_id_t)
  | ThEFinishIns : threadE unit
  | ThERegAccess : forall A, Arc.InsSem.regE A -> threadE A
  (** Load events *)
  | ThEInitMemLoadOps : Arc.mem_slc -> threadE (list mem_read_id_t)
  (* [ThESatMemLoadOpForwarding] returns a bool that indicates if the read
     was fully satisfied, and a list of iids that should be restarted. *)
  | ThESatMemLoadOpForwarding : mem_read_id_t -> threadE (bool * list mem_write_id_t)
  (* [ThESatMemLoadOpStorage] returns a list of iids that should be restarted. *)
  | ThESatMemLoadOpStorage : mem_read_id_t -> threadE (list mem_write_id_t)
  | ThECompleteLoadOps : threadE Arc.mem_slc_val
  (** Store events *)
  | ThEInitMemStoreOpFps : Arc.mem_slc -> threadE unit
  | ThEInstaMemStoreOpVals : Arc.mem_slc_val -> threadE unit
  | ThECommitStoreInstruction : threadE (list mem_write_id_t)
  (* [ThEPropagateStoreOp] returns a list of iids that should be restarted. *)
  | ThEPropagateStoreOp : mem_write_id_t -> threadE (list instruction_id_t)
  | ThECompleteStoreOps : threadE unit.

  Definition lift_regE {E} `{threadE -< E}
    : Arc.InsSem.regE ~> itree E :=
    fun _ e => trigger (ThERegAccess _ e).

  Definition denote_restarts {E} `{schedulerE instruction_id_t -< E}
    : ktree E (list instruction_id_t) unit :=
    ITree.iter (fun restarts =>
                  match restarts with
                  | [] => ret (inr tt)
                  | riid::restarts =>
                    trigger (Kill riid)
                    ;; trigger (Spawn riid)
                    ;; ret (inl restarts)
                  end).

  Definition lift_mem_read {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
             (slc : Arc.mem_slc)
    : itree E Arc.mem_slc_val :=
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
                       ;; '(is_sat, restarts) <- read
                       ;; 'tt <- denote_restarts restarts
                       ;; ret (inl (if (is_sat : bool) then
                                      List.remove Nat.eq_dec rid rids
                                    else rids))
                     end) rids.

  Definition lift_mem_write_fp {E} `{threadE -< E} `{nondetFinE -< E}
             (slc : Arc.mem_slc)
    : itree E unit :=
    trigger (ThEInitMemStoreOpFps slc).

  Definition lift_mem_write_val {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
             (val : Arc.mem_slc_val)
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
                       ;; restarts <- trigger (ThEPropagateStoreOp wid)
                       ;; 'tt <- denote_restarts restarts
                       ;; ret (inl (List.remove Nat.eq_dec wid wids))
                     end) wids.

  Definition lift_memE {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
    : Arc.InsSem.memE ~> itree E :=
    fun _ e =>
      match e with
      | Arc.InsSem.MemERead loc => (* FIXME: InsSem should use slc instead of loc *)
        lift_mem_read {| Arc.location := loc;
                         Arc.size := 1 |}
      | Arc.InsSem.MemEWriteFP loc => (* FIXME: InsSem should use slc instead of loc *)
        lift_mem_write_fp {| Arc.location := loc;
                               Arc.size :=1 |}
      | Arc.InsSem.MemEWriteVal val => lift_mem_write_val val
      end.

  Definition lift_ins_sem {E}
             `{threadE -< E} `{nondetFinE -< E}
             `{schedulerE instruction_id_t -< E}
    : itree Arc.InsSem.E ~> itree E :=
    fun _ it =>
      let h := case_ lift_regE lift_memE in
      interp h it.

  Definition new_instruction {E}
             `{wrapE threadE instruction_id_t -< E} `{nondetFinE -< E}
    : ktree (schedulerE instruction_id_t +' E)
            instruction_id_t
            (Types.result unit unit) :=
    fun iid =>
      let it : itree (threadE +' nondetFinE +' schedulerE instruction_id_t)
                     (Types.result unit unit) :=
          ast <- trigger ThEInsFetchAndDecode
          ;; next_iids <- trigger ThEInsNextLocs
          ;; ITree.iter (fun next_iids =>
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
      resum_it _ (scheduler Nat.eq_dec new_instruction
                            (fun r1 r2 => match r1, r2 with
                                       | Accept tt, Accept tt => Accept tt
                                       | _, _ => Reject tt
                                       end)
                            (Accept tt)
                            [(iid, new_instruction iid)]).
End Denote.

(*******************************************************************************)

Module State(Arc : ArcSig).
  Module DenoteA := Denote Arc.

  Record mem_read : Type :=
    mk_mem_read { read_id : mem_read_id_t;
                  read_fp : Arc.mem_slc;
                  read_kind : Arc.InsSem.mem_read_kind }.

  Record mem_reads_state :=
    mk_mem_reads_state { rs_footprint : Arc.mem_slc;
                         rs_reads : list mem_read;
                         rs_unsat_slcs : list (list Arc.mem_slc);
                         rs_reads_from : list (list (instruction_id_t * mem_write_id_t * Arc.mem_slc)) }.

  Record mem_write : Type :=
    mk_mem_write { write_id : mem_write_id_t;
                   write_fp : Arc.mem_slc;
                   write_val : Arc.mem_slc_val;
                   write_kind : Arc.InsSem.mem_read_kind }.

  Record mem_writes_state :=
    mk_mem_writes_state { ws_fps : list Arc.mem_slc;
                          ws_writes : list mem_write;
                          ws_has_propagated : list bool }.

  Record reg_read_state :=
    mk_reg_read_state { rrs_slc : Arc.InsSem.reg_slc;
                        rrs_feeding_addr : bool;
                        rrs_read_from : list (instruction_id_t * nat)
                                             (* the [nat] is an index into [ins_reg_writes.rws_slc]
                                                of the instruction pointed by the [instruction_id_t]. *)
                        rrs_val : option Arc.InsSem.reg_val }.

  Record reg_write_state :=
    mk_reg_write_state { rws_slc : Arc.InsSem.reg_slc;
                         rws_val : option Arc.InsSem.reg_val;
                         (* [rws_deps] is a concatination of all the
                            [rrs_read_from] of the instruction, when the
                            reg-write was performed. We assume that there is a
                            dataflow from those to this reg-write, and therefore
                            a dependency between the feeding instructions and
                            any instruction that reads from this
                            register-write. *)
                         rws_deps : list (instruction_id_t * nat);
                         rws_load_dep : bool }.

  Record decoded_instruction_state :=
    mk_decoded_instruction_state {
        (* statically analysed data about the instruction*)
        ins_kind: Arc.instruction_kind;

        ins_reg_reads : list reg_reads_state;
        ins_reg_writes : list reg_writes_state;

        reg_writes: list (Arc.InsSem.reg_ * (list register_write_dependency * register_value));

        ins_mem_reads: option mem_reads_state;
        ins_mem_writes: option mem_writes_state;

        ins_finished: bool }.

  Instance eta_decoded_instruction_state : Settable _ :=
    settable! mk_decoded_instruction_state <ins_kind; ins_regs_in; ins_regs_feeding_address; ins_regs_out; ins_mem_reads; ins_mem_writes; ins_finished>.

  Definition initial_decoded_instruction_state
             (ast : Arc.InsSem.ast)
    : decoded_instruction_state :=
    let '(regs_in, regs_feeding_address, regs_out) := Arc.InsSem.regs_from_ast ast in
    (* instruction_state: *)
    {| ins_kind := (Arc.instruction_kind_from_ast ast);
       ins_regs_in := regs_in;
       ins_regs_feeding_address := regs_feeding_address;
       ins_regs_out := regs_out;
       ins_mem_reads := None;
       ins_mem_writes := None;
       ins_finished := false |}.

  Definition instruction_state : Type := instruction_id_t *
                                         Arc.mem_loc *
                                         option decoded_instruction_state.

  Record state :=
    mk_state { next_iid : instruction_id_t;
               instruction_tree : tree instruction_state }.

  Instance eta_state : Settable _ :=
    settable! mk_state <next_iid; instruction_tree>.

  Definition initial_state (loc : Arc.mem_loc)
    : state :=
    {| next_iid := 1;
       instruction_tree := Tree (0, loc, None) [] |}.

  Variant storageE : Type -> Type :=
  | StEReadInstruction : Arc.InsSem.pc_t -> storageE Arc.InsSem.machine_code
  | StERead : mem_read_id_t -> storageE unit.

  Definition get_instruction_state {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E instruction_state :=
    let fix helper t :=
        let '(Tree ((iid', _, _) as i) ts) := t in
        if Nat.eqb iid' iid then Some i
        else
          match List.find (fun x => match x with None => false | _ => true end)
                          (List.map helper ts) with
          | Some x => x
          | None => None
          end
    in
    try_unwrap_option (helper s.(instruction_tree)) "get_instruction_state: Can't find iid".

  Definition get_dec_instruction_state {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E decoded_instruction_state :=
    '(_, _, ins) <- get_instruction_state iid s
    ;; try_unwrap_option ins "get_dec_instruction_state: instruction was not decoded yet".

  Definition update_dec_instruction_state (iid : instruction_id_t)
             (ins : decoded_instruction_state) (s : state)
    : state :=
    let fix helper t :=
        let '(Tree ((iid', loc, _) as i) ts) := t in
        if Nat.eqb iid' iid then Tree (iid, loc, Some ins) ts
        else Tree i (List.map helper ts)
    in
    s <| instruction_tree := helper s.(instruction_tree) |>.

  Definition try_read_reg_slc {E}
             (rslc : Arc.InsSem.reg_slc) (iid : instruction_id_t) (s : state)
    : itree E (state * Arc.InsSem.reg_val) :=
    ITree.spin.

  Definition try_write_reg_slc {E}
             (rslc : Arc.InsSem.reg_slc) (val : Arc.InsSem.reg_val)
             (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    ins <- get_dec_instruction_state iid s
    ;; update_dec_instruction_state iid () s

  Definition handle_reg_access {E} `{exceptE error -< E}
             {A} (e : Arc.InsSem.regE A) (iid : instruction_id_t) (s : state)
    : itree E (state * A) :=
    match e with
    | Arc.InsSem.RegERead rslc => try_read_reg_slc rslc iid s
    | Arc.InsSem.RegEWrite rslc rval => try_write_reg_slc rslc rval iid s
    end.

  Definition try_fetch_and_decode {E} `{storageE -< E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * Arc.InsSem.ast) :=
    '(_, loc, _) <- get_instruction_state iid s
    ;; mem_read_result <- trigger (StEReadInstruction loc)
    ;; code <- value_from_mem_read_result mem_read_result
    ;; ast <- Arc.InsSem.decode code
    ;; let ins := initial_decoded_instruction_state ast in
       let s := update_dec_instruction_state iid ins s in
       ret (s, ast).

  Definition try_get_next_locations {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * list instruction_id_t) :=
    iic <- get_instruction_in_context iid s
    ;; ins <- get_decoded_instruction_state iic
    ;; let next_pcs := Arc.InsSem.next_pc ins.(ins_loc) ins.(ins_ast) in
       let iids := List.seq s.(next_iid) (List.length next_pcs) in
       let iidpcs := List.combine iids next_pcs in
       let new_subtrees := List.map (fun (iid, pc) => Tree (ISUnfetched pc) []) iidpcs in
       let s := s <| next_iid := s.(next_iid) + (List.length next_pcs) |>
                  <| instruction_tree := apply_tree_context iic.(iic_context) iic.(iic_instruction) new_subtrees |> in
       ret (s, iids).

  Definition try_init_mem_load_ops {E} `{exceptE error -< E}
             (slc : Arc.mem_slc) (iid : instruction_id_t) (s : state)
    : itree E (state * list mem_read_id_t) :=
    throw NotImplemented.

  Definition try_write_forward {E} `{exceptE error -< E}
             (rid : mem_read_id_t) (iid : instruction_id_t) (s : state)
    : itree E (state * bool) :=
    throw NotImplemented.

  Definition try_sat_mem_load_op_from_storage {E} `{storageE -< E} `{exceptE error -< E}
             (rid : mem_read_id_t) (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    iic <- get_instruction_in_context iid s
    ;; ins <- get_decoded_instruction_state iic
    ;; rr <- get_mem_read_request rid ins
    ;; mem_read_result <- trigger (StoERead rr)
    ;; ins <- update_mem_read_request mem_read_result rid ins
    ;; let s := <| instruction_tree := apply_tree_context iic.(iic_context) (ISDecoded ins) iic.(iic_subtrees) |> in
       ret (s, tt).

  Definition try_complete_load_ops {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * mem_slc_val) :=
    iic <- get_instruction_in_context iid s
    ;; ins <- get_decoded_instruction_state iic
    ;; val <- get_mem_reads_value ins
    ;; ret (s, val).

  Definition try_finish_instruction {E} `{exceptE error -< E}
             (iid : instruction_id_t) (s : state)
    : itree E (state * unit) :=
    throw NotImplemented.

  Definition handle_threadE {E} `{storageE -< E} `{exceptE error -< E}
    : wrapE ThrDenote.threadE Thread.instruction_id_t ~>
            stateT state (itree E) :=
    fun _ e s =>
      let '(Wrap e iid) := e in
      match e with
      | ThEInsFetchAndDecode => try_fetch_and_decode iid s
      | ThEInsNextLocs => try_get_next_locations iid s
      | ThEFinishIns => try_finish_instruction iid s
      | ThERegAccess _ e => handle_reg_access e iid s
      (* Load events *)
      | ThEInitMemLoadOps slc => try_init_mem_load_ops slc iid s
      | ThESatMemLoadOpForwarding rid => throw NotImplemented
      | ThESatMemLoadOpStorage rid => try_sat_mem_load_op_from_storage rid iid s
      | ThECompleteLoadOps => try_complete_load_ops iid s
      (* Store events *)
      (* | ThEInitMemStoreOpFps : Arc.mem_slc -> threadE unit *)
      (* | ThEInstaMemStoreOpVals : Arc.mem_slc_val -> threadE unit *)
      (* | ThECommitStoreInstruction : threadE (list mem_write_id_t) *)
      (* | ThEPropagateStoreOp : mem_write_id_t -> threadE unit *)
      (* | ThECompleteStoreOps : threadE unit. *)
      end.



End State.
