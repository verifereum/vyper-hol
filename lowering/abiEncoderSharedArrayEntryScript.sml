(* Concrete JMP entry: the generated header has no selected PHI. *)
Theory abiEncoderSharedArrayEntry
Ancestors
  abiEncoderArrayLoopEntry abiEncoderArrayLoopHeader abiEncoderArrayLoopCode
  abiEncoderSharedArrayIndex abiEncoderSharedArrayHeader abiEncoderSharedContract
  abiEncoderExtendSim abiEncoderVarTransport abiDecoderVarExtend execEquivParamDefs
  abiEncoderRegisteredEffect abiScratchAddress abiScratchEffect abiEncoderMembersDefs
  abiEncoderArrayPrefix abiDecoderPrimitiveLoopEntry abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract abiDecoderLoop abiDecoderAllocation
  abiDecoderLoopRegisters exprLoweringProps venomMemDefs
  compileEnv venomState venomExecSemantics words list arithmetic

Theorem abi_encoder_array_jump_extend_state:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (jump_to label s) (jump_to label t)
Proof
  simp[abi_decoder_vars_extend_def, jump_to_def, vsr_frame_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encoder_array_loop_entry_extend:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_encoder_extend_sim ctx func initial (jump_to (FST labels) initial)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_encoder_array_loop_entry_sim >> simp[]) >>
  rpt strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  qexists_tac `jump_to (FST labels) t` >> conj_tac
  >- (irule abi_encoder_array_jump_extend_state >> asm_rewrite_tac []) >>
  `~t.vs_halted` by metis_tac[] >>
  irule abi_encoder_array_loop_entry_sim >> asm_simp_tac bool_ss [] >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem abi_encoder_shared_array_loop_enter:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  mem_word_at d initial.vs_memory = n2w (LENGTH avs) /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) 0 initial (jump_to (FST labels) initial) /\
  abi_encoder_extend_sim ctx func initial (jump_to (FST labels) initial)
Proof
  strip_tac >> drule_all abi_encoder_array_loop_entry_extend >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `abi_decoder_address_frame owner_st.cs_next_var initial (jump_to (FST labels) initial)` by
    simp[abi_decoder_address_frame_def, abi_decoder_operand_jump, jump_to_def] >>
  `fresh_vars_wrt limit_st (jump_to (FST labels) initial)` by simp[abi_decoder_fresh_jump] >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial
    (jump_to (FST labels) initial)` by (drule_all abi_scratch_address_effect >> simp[]) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) (jump_to (FST labels) initial)` by
    (drule_all abi_encoder_shared_input_address >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_array_index_def] >>
  simp[abi_encoder_array_prefix_empty, abi_encoder_cursor_jump,
    abi_decoder_operand_jump, jump_to_def, abi_encoder_registered_effect_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array entry admission, axiom or hypothesis"
  end) [abi_encoder_array_jump_extend_state, abi_encoder_array_loop_entry_extend,
    abi_encoder_shared_array_loop_enter];
