(* Rich interpretation of the neutral array-tail driver.  No member-prefix
   equality is used: the actual two-instruction array preparation is retained. *)
Theory abiEncoderSharedArraySpine
Ancestors
  abiEncoderArraySpine abiEncoderSharedMemberContract abiEncoderMemberSpineCompat
  abiEncoderArrayTail abiEncoderSharedContract abiEncoderMemberPhaseRaw abiScratchMemberContract
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup abiEncoderMemberPhaseEffect abiEncoderRegisteredEffect
  abiEncoderExtendSim abiScratchEffect abiScratchEncoderContract abiScratchChild abiDecoderAllocation
  emitHelper emitHelperProps venomInst venomExecSemantics
  exprLoweringProps compileEnv venomState venomMemDefs words list rich_list

Theorem abi_encoder_array_spine_shared_pre:
  abi_encode_array_tail data_op dp st = (ops,p) /\
  abi_encoder_shared ei /\
  abi_encoder_shared_input (ei,at,av) (st,src,data_op) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ ce.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+off)
    (first,last,b,cap,limit_st) (ei,SND ops,src,p,ce,len) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand data_op initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var data_op` by fs[abi_encoder_shared_input_def] >>
  drule_all abi_encoder_member_tail_transport >> strip_tac >>
  drule_all abi_encoder_array_tail_raw_control >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  `st.cs_next_var <= p.cs_next_var` by decide_tac >>
  drule_all abi_encoder_spine_shared_input_address >> disch_tac >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  simp[abi_encoder_spine_shared_pre_def]
QED

Theorem abi_encoder_array_spine_cursor_saved:
  abi_encode_array_tail data_op dp st = (ops,p) /\
  eval_operand data_op initial = SOME (n2w d) /\
  eval_operand dp initial = SOME (n2w slot) /\
  eval_operand head initial = SOME (n2w h) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  abi_decoder_operand_live st.cs_next_var dp /\
  abi_decoder_operand_live st.cs_next_var head /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  first <= site /\ site < last /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_scratch_member_cursor_saved (head,FST ops,dp,h,off,slot,site)
    (first,last,b,cap,limit_st) (ei,SND ops,src,p,ce,len) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_tail_transport >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  simp_tac bool_ss [abi_scratch_member_cursor_saved_def] >>
  rpt conj_tac
  >- (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[])
  >- asm_rewrite_tac []
  >- (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  fs[abi_decoder_address_frame_def] >> decide_tac
QED

(* Instantiate the one actual driver with genuine rich children.  The saved
   cursor is retained in the callback post, never reconstructed from a weak run. *)
Theorem abi_encoder_array_spine_shared_run:
  abi_encode_array_tail data_op dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND ops,src,p,ce,len) /\
  abi_encode_child_suffix head dp (FST ops) len ce = (out,en) /\
  eval_operand data_op initial = SOME (n2w d) /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  h < dimword (:256) /\ en.cs_next_var <= limit_st.cs_next_var /\
  (!ready. abi_encoder_member_phase_raw st p initial ready ==>
    abi_encoder_shared_member_dynamic_pre (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (head,FST ops,dp,h,off,slot,site)
      (ei,SND ops,src,p,ce,len) ready) ==>
  ?ready encoded actual.
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_call (\c. abi_encoder_extend_sim ctx func)
      (ei,SND ops,src,p,ce,len) ready encoded /\
    abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (head,FST ops,dp,h,off,slot,site)
      (ei,SND ops,src,p,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual
Proof
  strip_tac >>
  irule abi_encoder_array_spine_dynamic_run >>
  conj_tac
  >- (qexistsl_tac [`abi_encoder_shared_member_dynamic_pre
        (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
        (head,FST ops,dp,h,off,slot,site)`, `func`] >>
      asm_rewrite_tac [] >> rpt strip_tac >>
      irule abi_encoder_shared_member_dynamic_run >> asm_rewrite_tac []) >>
  qexistsl_tac [`d`,`data_op`,`dp`,`head`,`limit_st`,`off`,`out`,`slot`] >>
  asm_rewrite_tac [] >> rpt strip_tac >>
  drule_all abi_encoder_shared_member_dynamic_cursor_input >> simp[]
QED

Theorem abi_encoder_array_spine_tail_opcodes:
  abi_encode_array_tail data_op dp st = (ops,p) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st p)
Proof
  simp[abi_encode_array_tail_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_spine_tail_registered:
  abi_encode_array_tail data_op dp st = (ops,p) /\
  eval_operand data_op initial = SOME (n2w d) /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_tail_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_array_spine_tail_opcodes >> simp[]) >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_spine_tail_extend_sim:
  abi_encode_array_tail data_op dp st = (ops,p) /\ fn_has_code st p func /\
  abi_encoder_member_phase_raw st p initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule abi_encode_array_tail_shape >> strip_tac >>
  irule abi_encoder_member_phase_extend_sim >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> fs[EVERY_MEM]
QED

Theorem abi_encoder_array_spine_shared_effects:
  abi_encode_array_tail data_op dp st = (ops,p) /\
  eval_operand data_op initial = SOME (n2w data_base) /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st p initial ready /\
  abi_decoder_address_frame next initial ready /\
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  h < dimword (:256) /\ en.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw ce en encoded actual /\
  first <= lo /\ hi <= last /\ lo <= p.cs_next_id /\ ce.cs_next_id <= hi /\
  next <= p.cs_next_var /\ next <= ce.cs_next_var /\
  site IN abi_decoder_ids lo hi /\ FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  d <= h /\ h+32 <= d+extent /\ d <= q /\ q+LENGTH (enc at av) <= d+extent ==>
  abi_scratch_effect first last lo hi next limit_st d extent b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] initial actual /\
  (alloca_inv initial ==> alloca_inv actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand len encoded = SOME (n2w (LENGTH (enc at av))) /\
   fresh_vars_wrt limit_st encoded /\ (alloca_inv ready ==> alloca_inv encoded)` by
    fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def] >>
  drule_all abi_encoder_spine_cursor_post >> disch_tac >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  conj_tac
  >- (irule (cj 1 abi_scratch_child_effect) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `site` >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] initial ready /\
   (alloca_inv initial ==> alloca_inv ready)` by
    (drule_all abi_encoder_array_spine_tail_registered >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] ready encoded` by
    (drule_all abi_encoder_spine_shared_registered_window >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] encoded actual /\
   (alloca_inv encoded ==> alloca_inv actual)` by
    (drule_all abi_encoder_member_cursor_registered >> simp[]) >>
  conj_tac >- (irule abi_encoder_registered_effect_trans >>
    qexists_tac `ready` >> simp[] >>
    irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >> simp[]) >>
  metis_tac[]
QED

Theorem abi_encoder_array_spine_shared_sim:
  abi_encode_array_tail data_op dp st = (ops,p) /\ fn_has_code st p func /\
  abi_encoder_member_phase_raw st p initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\ fn_has_code ce en func /\
  abi_encoder_member_phase_raw ce en encoded actual ==>
  abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_spine_tail_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `~encoded.vs_halted /\ encoded.vs_current_bb = ce.cs_current_bb /\
   encoded.vs_inst_idx = LENGTH ce.cs_current_insts /\
   abi_encoder_extend_sim ctx func ready encoded` by
    fs[abi_encoder_shared_endpoint_def] >>
  drule_all abi_encoder_spine_suffix_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> simp[] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `encoded` >> simp[]
QED

val _ =
  if List.exists (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
    ["abiScratchEncoderRecursive", "abiEncoderCorrectRecursive", "abiEncoderProps"]
  then raise Fail "shared array spine imports recursive execution owner" else ();
val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array spine admission, axiom or hypothesis"
  end) [abi_encoder_array_spine_shared_pre, abi_encoder_array_spine_cursor_saved,
    abi_encoder_array_spine_shared_run, abi_encoder_array_spine_tail_opcodes,
    abi_encoder_array_spine_tail_registered, abi_encoder_array_spine_tail_extend_sim,
    abi_encoder_array_spine_shared_effects, abi_encoder_array_spine_shared_sim];
