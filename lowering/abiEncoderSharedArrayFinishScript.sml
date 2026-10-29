(* Fixed parent bookkeeping at a supplied raw endpoint; no recursive execution. *)
Theory abiEncoderSharedArrayFinish
Ancestors
  abiEncoderArrayFinish abiEncoderArrayScalarCode abiEncoderArrayPhases
  abiEncoderMemberPhaseRaw abiEncoderMemberPhaseEffect abiEncoderRegisteredEffect
  abiEncoderExtendSim abiScratchEffect abiDecoderFootprint abiDecoderFrameCompose
  abiDecoderAllocation abiDecoderFrame abiDecoderContract abiDecoderReentry
  abiDecoderDynamicLoopSetup exprLoweringProps compileEnv emitHelper emitHelperProps venomInst
  venomState venomExecSemantics venomMemDefs instIdxIndep words list rich_list arithmetic

Theorem abi_encoder_array_finish_raw_transport:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (old_word+size_word) /\ mload slot ready = old_word+size_word /\
  fresh_vars_wrt limit_st ready /\ abi_decode_frame slot 32 initial ready /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op ready = SOME w)
Proof
  strip_tac >> drule_all abi_encode_array_finish_sequence >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def, eval_op_inst_idx, fresh_vars_wrt_def,
      abi_decode_frame_def, mload_def] >> metis_tac[]
QED

Theorem abi_encoder_array_finish_opcodes:
  abi_encode_array_finish parent_ptr size_op st = (out,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final)
Proof
  simp[abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_finish_registered:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  id IN ids /\ FLOOKUP initial.vs_allocas id = SOME (slot,32) ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_finish_raw_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_array_finish_opcodes >> simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [abi_encoder_registered_effect_def] >>
      gvs[abi_decode_frame_def] >> rpt strip_tac >>
      `a < slot \/ slot+32 <= a` by
        (qpat_x_assum `!i b sz. _` (qspecl_then [`id`,`slot`,`32`] mp_tac) >> simp[]) >>
      first_x_assum irule >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_finish_extend:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  abi_encoder_member_phase_raw st final initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_shared_array_finish_effect:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_encoder_array_finish_raw_transport >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    fs[abi_decode_frame_footprint] >>
  `site IN abi_decoder_ids lo hi` by simp[abi_decoder_ids_def] >>
  drule_all abi_encoder_array_finish_registered >>
  disch_then (qspecl_then [`[(d,sz)]`] strip_assume_tac) >>
  drule_all abi_encoder_array_finish_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac bool_ss [] >> irule abi_scratch_single_write >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  qexistsl_tac [`site`,`slot`] >> asm_rewrite_tac []
QED

Theorem abi_encoder_array_finish_preserves_output:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  mem_bytes_at d len initial.vs_memory = bytes /\
  abi_footprint_disjoint d len [(slot,32)] ==>
  mem_bytes_at d len ready.vs_memory = bytes /\
  eval_operand out ready = SOME (n2w len) /\ mload slot ready = n2w len
Proof
  strip_tac >> drule_all abi_encoder_array_finish_raw_transport >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] initial ready` by
    fs[abi_decode_frame_footprint] >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array finish admission, axiom or hypothesis"
  end) [abi_encoder_array_finish_raw_transport, abi_encoder_array_finish_opcodes,
    abi_encoder_array_finish_registered, abi_encoder_array_finish_extend,
    abi_encoder_shared_array_finish_effect, abi_encoder_array_finish_preserves_output];
