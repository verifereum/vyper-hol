(* Pure physical interpretation of common child certificates. *)
Theory abiScratchMemberInterpret
Ancestors
  abiEncoderChildCapability abiSiteEncoderContract abiSiteAllocation emitHelperProps
  abiScratchMemberContract abiScratchMemberAdapter abiEncoderMemberPhaseExec
  abiScratchChild abiEncoderChildCode
  abiScratchFootprint abiScratchFrameCompose abiEncoderChildEffect
  abiEncoderChildPrefix abiEncoderMemberPhaseEffect abiEncoderExtendSim abiEncoderInput
  abiEncoderMemberSpine abiEncoderChildContext abiEncoderAddressReach
  abiScratchAddress abiScratchAfterAddress abiScratchEffect abiScratchEncoderContract
  abiEncoderMemberPhaseRaw abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderProtectedScratch abiDecoderArrayInitExec abiDecoderAllocation abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_member_static_input:
  abi_encoder_child_capability A guard ei /\
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  (!head prepared. emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) ==>
    guard prepared en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_encoder_input ei at av st src dst sb source_cap d output_size A b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_site_budget A b cap initial /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_child_ready (at,av,sb,source_cap,d+offset) (A,b,cap,limit_st) guard)
    (abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d+offset) (A,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_site_encoder_input_def] >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  qexistsl_tac [`head`,`prepared`,`n2w d`] >>
  asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >>
  rpt strip_tac >> drule_all abi_site_member_static_place_raw_transport >> strip_tac >>
  drule_all abi_site_address >>
  disch_then (qspecl_then [`A`, `[]`] strip_assume_tac) >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >> fs[abi_encoder_child_ready_def, abi_encoder_child_pre_def]
QED

Theorem abi_site_member_static_input:
  abi_site_encoder ei /\
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_encoder_input ei at av st src dst sb source_cap d output_size A b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_site_budget A b cap initial /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_child_ready (at,av,sb,source_cap,d+offset) (A,b,cap,limit_st)
      (\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A))
    (abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d+offset) (A,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_child_capability_site >> disch_then (qspec_then `A` assume_tac) >>
  `!head prepared. emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) ==>
    abi_decoder_emitted_sites prepared.cs_next_id en.cs_next_id prepared en SUBSET A` by
    (rpt strip_tac >> drule_all abi_encoder_static_child_site_guard >> simp[]) >>
  irule (SRULE [] (Q.INST
    [`guard` |-> `\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A`]
    abi_encoder_member_static_input)) >> asm_rewrite_tac[] >>
  qexists_tac `output_size` >> asm_rewrite_tac[]
QED

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
  drule abi_encoder_child_capability_interval >>
  disch_then (qspecl_then [`last`,`first`] assume_tac) >>
  `!head prepared. emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) ==>
    first <= prepared.cs_next_id /\ en.cs_next_id <= last` by
    (rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  `abi_site_encoder_input ei at av st src dst sb source_cap d output_size
    (abi_decoder_ids first last) b cap initial /\
   abi_site_budget (abi_decoder_ids first last) b cap initial` by
    simp[abi_site_encoder_input_interval, abi_site_budget_interval] >>
  drule_all (SRULE [] (Q.INST
    [`guard` |-> `\st en. first <= st.cs_next_id /\ en.cs_next_id <= last`]
    abi_encoder_member_static_input)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  fs[abi_encoder_spine_child_input_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[abi_encoder_child_ready_def, abi_encoder_child_pre_def,
    abi_scratch_member_core_pre_def, abi_site_encoder_input_interval, abi_site_budget_interval]
QED
Theorem abi_encoder_member_static_output:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_encoder_input ei at av st src dst sb source_cap d output_size A b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ abi_site_budget A b cap initial /\
  abi_encoder_spine_child_output
    (abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d+offset) (A,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial t ==>
  mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  abi_site_encoder_effect A st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st (d+offset) (LENGTH (enc at av)) b cap initial t /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def, abi_encoder_child_post_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[] >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `p.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= p.cs_next_var /\
    st.cs_next_id <= p.cs_next_id` by decide_tac >>
  drule_all abi_site_member_static_place_raw_transport >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_site_encoder_input_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `st.cs_next_id <= p.cs_next_id /\ en.cs_next_id <= en.cs_next_id /\
    d <= d+offset /\ (d+offset)+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  `abi_site_encoder_effect A st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st (d+offset) (LENGTH (enc at av)) b cap initial t` by
    (irule abi_site_effect_after_address >>
     qexistsl_tac [`d+offset`, `en.cs_next_id`, `st.cs_next_id+1`,
       `st.cs_next_var+1`, `LENGTH (enc at av)`, `r`] >> simp[]) >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >> simp[]
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
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_spine_child_output
    (abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (abi_decoder_ids first last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial t` by
    (qpat_x_assum `abi_encoder_spine_child_output _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_spine_child_output_def] >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     `first <= p.cs_next_id` by decide_tac >>
     qexistsl_tac [`head`, `p`, `r`] >>
     fs[abi_encoder_child_post_def, abi_scratch_member_core_post_def,
       abi_site_encoder_effect_interval]) >>
  `abi_site_encoder_input ei at av st src dst sb source_cap d output_size
    (abi_decoder_ids first last) b cap initial /\
   abi_site_budget (abi_decoder_ids first last) b cap initial` by
    simp[abi_site_encoder_input_interval, abi_site_budget_interval] >>
  drule_all abi_encoder_member_static_output >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st (d+offset) (LENGTH (enc at av)) b cap initial t` by
    metis_tac[abi_site_encoder_effect_interval] >>
  `abi_decode_footprint_frame
    ([(d+offset,LENGTH (enc at av))] ++ abi_decoder_child_scratch
      (abi_decoder_ids st.cs_next_id en.cs_next_id) b cap initial) initial t` by
    fs[abi_scratch_effect_def] >>
  simp[] >> irule abi_scratch_effect_widen >>
  qexistsl_tac [`d+offset`, `en.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`,
    `LENGTH (enc at av)`] >> simp[]
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

Theorem abi_scratch_member_dynamic_output_detailed:
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\ fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand dp initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dp /\
  ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_scratch_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,src,ho,dp,st,en,out) initial t ==>
  mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
  mem_word_at (d+ho) t.vs_memory = n2w off /\
  mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  abi_scratch_effect first last lo en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial t /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~t.vs_halted /\ abi_decode_sim ctx func initial t /\
  abi_decode_footprint_frame
    ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
      abi_decoder_child_scratch (abi_decoder_ids lo en.cs_next_id) b cap initial) initial t
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >> gvs[] >> (
  imp_res_tac abi_scratch_member_dynamic_saved >>
  fs[abi_scratch_member_dynamic_post_def, abi_scratch_member_core_post_def,
    abi_encoder_spine_core_code_def] >> gvs[] >>
  rename1 `abi_encoder_member_phase_raw st prepared initial r` >>
  rename1 `compile_abi_encode_to_buf _ src ei prepared = (child_len,child_end)` >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var /\
    st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  `site IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]) >>
  `slot < dimword (:256)` by decide_tac >>
  `d+output_size < dimword (:256)` by fs[abi_scratch_input_def] >>
  `abi_decoder_operand_live child_end.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_scratch_dynamic_prepare_raw_transport >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap r u` by fs[abi_scratch_effect_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial u` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap u)` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `u:venom_state`,
      `ids` |-> `abi_decoder_ids first last`, `p` |-> `d:num`, `n` |-> `output_size:num`]
      abi_scratch_disjoint_advance) >> impl_tac >- fs[abi_scratch_input_def] >> simp[]) >>
  `d <= d+ho /\ d+ho+32 <= d+off` by decide_tac >>
  drule_all abi_scratch_dynamic_finish_raw_transport >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lo <= prepared.cs_next_id /\ child_end.cs_next_id <= en.cs_next_id /\
    site IN abi_decoder_ids lo en.cs_next_id /\ d <= d+off /\
    (d+off)+LENGTH (enc at av) <= d+output_size /\ d+ho+32 <= d+output_size` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_scratch_effect first last prepared.cs_next_id child_end.cs_next_id prepared.cs_next_var
    limit_st (d+off) (LENGTH (enc at av)) b cap r u` by fs[] >>
  drule_all abi_scratch_child_effect >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (assume_tac o MATCH_MP abi_encoder_extend_sim_sim) >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `r` >> asm_simp_tac bool_ss [] >>
     irule abi_decode_sim_trans >> qexists_tac `u` >> asm_simp_tac bool_ss []) >>
  fs[])
QED

Theorem abi_scratch_member_dynamic_output:
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\ fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand dp initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dp /\
  ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_scratch_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,src,ho,dp,st,en,out) initial t ==>
  mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
  mem_word_at (d+ho) t.vs_memory = n2w off /\
  mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  abi_scratch_effect first last lo en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial t /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_member_dynamic_output_detailed >> simp_tac bool_ss []
QED

val _ = List.app (fn theory => List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean member dependency: " ^ theory ^ "." ^ name)
  end) (DB.thms theory))
  ["compilerOccurrences", "abiDecoderSiteMembership", "abiEncoderChildContext",
   "abiScratchInput", "abiScratchChild", "abiScratchAddress", "abiEncoderMemberPhaseExec",
   "abiScratchAfterAddress", "abiScratchMemberInterpret"];
