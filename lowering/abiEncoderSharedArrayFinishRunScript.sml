(* Execute the existing scalar finish sequence and attach rich observations. *)
Theory abiEncoderSharedArrayFinishRun
Ancestors
  abiEncoderSharedArrayFinish abiEncoderArrayFinish abiEncoderSequence abiEncoderArrayScalarCode
  abiEncoderMemberPhaseRaw abiEncoderRegisteredEffect abiEncoderExtendSim
  abiScratchEffect abiScratchFootprint abiScratchEncoderContract abiDecoderAllocation
  abiDecoderFrame abiDecoderFootprint abiDecoderProtectedScratch abiDecoderContract abiDecoderReentry compileEnv venomState
  words list arithmetic

Theorem abi_encoder_shared_array_finish_run:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = 0w /\
  eval_operand size_op initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  mem_bytes_at d len initial.vs_memory = bytes /\ len <= sz /\
  abi_footprint_disjoint d sz (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\
    eval_operand out actual = SOME (n2w len) /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[]) >>
  `abi_footprint_disjoint d len [(slot,32)]` by
    (fs[abi_footprint_disjoint_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  drule_all abi_encode_array_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_encoder_member_phase_raw st final initial actual` by
    (simp[abi_encoder_member_phase_raw_def] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_encoder_array_finish_preserves_output >> strip_tac >>
  drule_all abi_encoder_shared_array_finish_effect >>
  disch_then (qspecl_then [`sz`,`d`,`ctx`] strip_assume_tac) >>
  qexists_tac `actual` >> gvs[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared finish run admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_finish_run];
