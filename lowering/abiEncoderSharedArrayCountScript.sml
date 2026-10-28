(* Count-copy observations at the one supplied concrete raw endpoint. *)
Theory abiEncoderSharedArrayCount
Ancestors
  abiEncoderArrayCount abiDecoderArrayHeader abiDecoderArrayLoopInit abiDecoderGuards
  abiEncoderMemberPhaseRaw abiEncoderMemberPhaseEffect abiEncoderRegisteredEffect
  abiEncoderExtendSim abiScratchLeafEffect abiScratchEffect abiDecoderFootprint
  abiDecoderAllocation abiDecoderFrame abiDecoderFrameCompose abiDecoderContract
  abiDecoderReentry abiDecoderDynamicLoopSetup exprLoweringProps compileEnv emitHelper
  emitHelperProps venomInst venomState venomExecSemantics venomMemDefs instIdxIndep
  abiEncoderSharedArrayInput abiEncoderSharedContract abiEncoderOpenInputFrame
  abiEncoderArrayPrefix abiEncoderArrayFrame abiEncoderOpenInput contractABI valueEncoding valueEncodingProps
  words list rich_list arithmetic

Theorem abi_encoder_array_count_raw_transport:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand cnt ready = SOME (mload sb initial) /\
  mem_word_at d ready.vs_memory = mload sb initial /\
  fresh_vars_wrt limit_st ready /\ abi_decode_frame d 32 initial ready /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op ready = SOME w)
Proof
  strip_tac >> drule_all abi_encoder_array_count_copy_sequence >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def, eval_op_inst_idx, fresh_vars_wrt_def,
    abi_decode_frame_def] >> metis_tac[]
QED

Theorem abi_encoder_array_count_opcodes:
  abi_decode_array_header dst src MLOAD st = (cnt,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final)
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_count_registered:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\ 32 <= sz ==>
  abi_encoder_registered_effect ids [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_count_raw_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_array_count_opcodes >> simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [abi_encoder_registered_effect_def] >>
      gvs[abi_decode_frame_def] >> rpt strip_tac >>
      first_x_assum irule >> fs[] >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_count_extend:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\ fn_has_code st final func /\
  abi_encoder_member_phase_raw st final initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >>
  drule (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  simp[abi_decode_source_opcode_def, EVERY_CONJ] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)` by
    fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_shared_array_count_effect:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\ 32 <= sz /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_encoder_array_count_raw_transport >> strip_tac >>
  drule_all abi_encoder_array_count_registered >>
  disch_then (qspec_then `abi_decoder_ids lo hi` strip_assume_tac) >>
  drule_all abi_encoder_array_count_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac bool_ss [] >> irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >>
  irule abi_decode_frame_widen >> qexistsl_tac [`d`,`32`] >> simp[]
QED

Theorem abi_encoder_shared_array_count_input_facts:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s ==>
  mload sb s = n2w (LENGTH avs) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ abi_footprint_disjoint sb source_cap [(d,32)]
Proof
  strip_tac >> drule abi_encoder_shared_array_input_facts >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs` by
    (drule abi_encoder_structural_list_layout >> simp[]) >>
  drule abi_encoder_open_array_length >> disch_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  gvs[mem_word_at_eq_mload, abi_encoder_zero_aware_separation, Excl "enc_def"] >>
  simp[abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_encoder_shared_array_count_input:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (final,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) ready /\
  abi_encoder_array_prefix ty avs 0 d ready.vs_memory /\
  abi_decoder_operand_live final.cs_next_var cnt /\ eval_operand cnt ready = SOME (n2w (LENGTH avs))
Proof
  strip_tac >> drule abi_encoder_shared_array_count_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule_all abi_encoder_array_count_raw_transport >> strip_tac >>
  drule abi_encoder_array_count_live >> disch_tac >>
  `abi_decode_footprint_frame [(d,32)] initial ready` by fs[abi_decode_frame_footprint] >>
  `mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap ready.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[]) >>
  `abi_encoder_open_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap ready.vs_memory` by
    (drule_all abi_encoder_open_input_mem_agree >> simp[]) >>
  `st.cs_next_var <= final.cs_next_var` by
    (drule (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
     simp[abi_decode_source_opcode_def]) >>
  `eval_operand src ready = SOME (n2w sb) /\ eval_operand dst ready = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live final.cs_next_var src /\ abi_decoder_operand_live final.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def, abi_encoder_array_prefix_empty] >>
  fs[abi_decoder_child_scratch_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array count admission, axiom or hypothesis"
  end) [abi_encoder_array_count_raw_transport, abi_encoder_array_count_opcodes,
    abi_encoder_array_count_registered, abi_encoder_array_count_extend,
    abi_encoder_shared_array_count_effect, abi_encoder_shared_array_count_input_facts,
    abi_encoder_shared_array_count_input];
