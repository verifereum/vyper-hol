(* Pure physical interpretation of common child certificates. *)
Theory abiScratchMemberInterpret
Ancestors
  abiScratchMemberContract abiScratchMemberAdapter abiEncoderMemberPhaseExec
  abiEncoderMemberSpine abiEncoderChildContext abiEncoderAddressReach
  abiScratchAddress abiScratchAfterAddress abiScratchEffect abiScratchEncoderContract
  abiEncoderMemberPhaseRaw abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderProtectedScratch abiDecoderArrayInitExec abiDecoderAllocation abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding venomState words list arithmetic

Theorem abi_scratch_member_static_input:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_core_pre (at,av,sb,source_cap,d+offset) (first,last,b,cap,limit_st))
    (abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id`
    by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  qexistsl_tac [`head`,`prepared`,`n2w d`] >>
  asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >>
  rpt strip_tac >> drule_all abi_scratch_member_static_place_raw_transport >> strip_tac >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  `abi_decoder_budget first last b cap r` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `r:venom_state`]
      abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >> fs[abi_scratch_member_core_pre_def]
QED

Theorem abi_scratch_member_static_output:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  first <= st.cs_next_id /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decoder_budget first last b cap initial /\
  abi_encoder_spine_child_output
    (abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial t ==>
  mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  abi_decode_footprint_frame
    ([(d+offset,LENGTH (enc at av))] ++ abi_decoder_child_scratch
      (abi_decoder_ids st.cs_next_id en.cs_next_id) b cap initial) initial t /\
  abi_scratch_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial t /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def, abi_scratch_member_core_post_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[] >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `p.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= p.cs_next_var /\
    st.cs_next_id <= p.cs_next_id` by decide_tac >>
  drule_all abi_scratch_member_static_place_raw_transport >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `st.cs_next_id <= p.cs_next_id /\ en.cs_next_id <= en.cs_next_id /\
    d <= d+offset /\ (d+offset)+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  `abi_scratch_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
    limit_st (d+offset) (LENGTH (enc at av)) b cap r t` by fs[] >>
  drule_all abi_scratch_spine_frame_after_address >> disch_tac >>
  drule_all (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `en.cs_next_id`,
    `d` |-> `d:num`, `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >> disch_tac >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  fs[listTheory.APPEND]
QED

Theorem abi_scratch_member_dynamic_input:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\ fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand dp initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dp /\
  ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_dynamic_pre (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (abi_scratch_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,src,ho,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >> gvs[] >> (
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d) /\ abi_decoder_operand_live st.cs_next_var dst`
    by fs[abi_scratch_input_def] >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]) >>
  `slot < dimword (:256)` by decide_tac >>
  `d+ho < dimword (:256)` by (fs[abi_scratch_input_def] >> decide_tac) >>
  `abi_decoder_operand_live prepared.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  qexistsl_tac [`ops`,`prepared`,`child_len`,`child_end`,`d`,`slot`,`off`] >>
  asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >> conj_tac
  >- (rpt strip_tac >> drule_all abi_scratch_dynamic_prepare_raw_transport >> strip_tac >>
      fs[abi_scratch_member_dynamic_pre_def, abi_scratch_member_core_pre_def,
        abi_scratch_member_cursor_saved_def, abi_decoder_address_frame_def]) >>
  rpt strip_tac >>
  qpat_assum `abi_scratch_member_dynamic_post _ _ _ _ _ _ _` (fn post_th =>
  qpat_assum `d+ho < dimword (:256)` (fn head_bound_th =>
  qpat_assum `slot < dimword (:256)` (fn slot_bound_th =>
  qpat_assum `en.cs_next_var <= limit_st.cs_next_var` (fn final_bound_th =>
    rpt (pop_assum kall_tac) >>
    metis_tac [abi_scratch_member_dynamic_cursor_input, post_th,
      head_bound_th, slot_bound_th, final_bound_th])))))
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "scratch child interpretation has an admission, axiom or hypothesis"
  end) [abi_scratch_member_static_input, abi_scratch_member_static_output,
    abi_scratch_member_dynamic_input];
