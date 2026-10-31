(* Rich child requests at supplied member-generator endpoints. *)
Theory abiEncoderSharedMembersRequest
Ancestors
  abiEncoderSharedMembersIndex abiEncoderSharedMemberContract abiEncoderMemberSpineCompat
  abiEncoderMemberSpine abiEncoderMemberPhaseRaw abiEncoderChildContext
  abiEncoderMemberPhaseExec abiEncoderAddressReach abiEncoderSharedContract
  abiEncoderMembersDefs abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderAllocation abiDecoderProtectedScratch abiEncoderChildPrefix
  abiScratchMemberContract compileEnv venomState words list arithmetic

Theorem abi_encoder_shared_member_static_input:
  abi_encoder_shared ei /\ compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+offset) (first,last,b,cap,limit_st))
    (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id`
    by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_shared_input_def] >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  qexistsl_tac [`head`,`prepared`,`n2w d`] >>
  asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >>
  rpt strip_tac >> irule abi_encoder_spine_static_shared_pre >>
  asm_rewrite_tac [] >> qexistsl_tac [`dst`,`initial`,`output_size`,`st`] >>
  asm_rewrite_tac []
QED

Theorem abi_encoder_shared_members_static_request:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,F)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_encoder_shared_input (ei,ty,av) (p,elem_src,dst) (sb+so,mz)
    (d,sz) (first,last,b,cap) r /\
  compile_abi_encode_child dst elem_src ei F ho dp p = (len,ce) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_spine_shared_pre (ty,av,sb+so,mz,d+ho) (first,last,b,cap,limit_st))
    (abi_encoder_spine_shared_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_shared_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_shared_members_inv_layout)) >> strip_tac >>
  `ho+LENGTH (enc ty av) <= sz` by decide_tac >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  `first <= p.cs_next_id` by decide_tac >>
  drule_all abi_encoder_shared_member_static_input >> simp[]
QED

Theorem abi_encoder_shared_member_dynamic_input:
  abi_encoder_shared ei /\ compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\ fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dp /\
  ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_shared_member_dynamic_pre (at,av,sb,source_cap,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,src,ho,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >> gvs[] >> (
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d) /\ abi_decoder_operand_live st.cs_next_var dst`
    by fs[abi_encoder_shared_input_def] >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]) >>
  `slot < dimword (:256)` by decide_tac >>
  `d+ho < dimword (:256)` by (fs[abi_encoder_shared_input_def] >> decide_tac) >>
  `abi_decoder_operand_live prepared.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  qexistsl_tac [`ops`,`prepared`,`child_len`,`child_end`,`d`,`slot`,`off`] >>
  asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >> conj_tac
  >- (rpt strip_tac >>
      `abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+off)
        (first,last,b,cap,limit_st)
        (ei,SND (SND ops),src,prepared,child_end,child_len) r` by
        (irule abi_encoder_spine_dynamic_shared_pre >> asm_rewrite_tac [] >>
         qexistsl_tac [`dp`,`dst`,`ho`,`initial`,`output_size`,`slot`,`st`] >>
         asm_rewrite_tac []) >>
      drule_all abi_encoder_member_prefix_transport >> strip_tac >>
      drule abi_encode_child_prefix_live >> strip_tac >>
      fs[abi_encoder_shared_member_dynamic_pre_def, abi_scratch_member_cursor_saved_def,
        abi_decoder_address_frame_def]) >>
  rpt strip_tac >> irule abi_encoder_shared_member_dynamic_cursor_input >>
  asm_rewrite_tac [] >> goal_assum (drule_at Any) >> asm_rewrite_tac [])
QED

Theorem abi_encoder_shared_members_dynamic_request:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,T)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_encoder_shared_input (ei,ty,av) (p,elem_src,dst) (sb+so,mz)
    (d,sz) (first,last,b,cap) r /\
  compile_abi_encode_child dst elem_src ei T ho dp p = (len,ce) /\
  abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_shared_member_dynamic_pre (ty,av,sb+so,mz,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (abi_encoder_shared_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_shared_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`] abi_encoder_shared_members_inv_layout)) >> strip_tac >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  `active` by fs[EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= sz` by decide_tac >>
  `abi_decoder_operand_live p.cs_next_var dp /\
    eval_operand dp r = SOME (n2w slot) /\ mload slot r = n2w off /\
    first <= site /\ site < p.cs_next_id /\ FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    (qpat_assum `active` (fn ath =>
       qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
         (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def,ath])) >>
     asm_rewrite_tac []) >>
  drule_all abi_encoder_shared_member_dynamic_input >> simp[]
QED
