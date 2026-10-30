Theory abiEncoderSharedMembersEndpoint
Ancestors
  abiEncoderSharedMemberContract abiEncoderMemberSpineCompat abiEncoderSharedContract
  abiEncoderScratchTransport abiEncoderSharedSuffix abiEncoderChildContext abiEncoderMemberSpine
  abiEncoderAddressReach abiScratchEffect abiScratchEncoderContract abiDecoderDynamicLoopSetup
  abiScratchFootprint abiDecoderContract abiDecoderLoop abiScratchMemberAdapter
  abiEncoderChildSuffixReach abiScratchChild abiDecoderReentry abiDecoderProtectedScratch
  abiDecoderAllocation abiEncoderMemberPhaseRaw abiEncoderMemberPhaseExec
  abiEncoderRegisteredEffect abiEncoderExtendSim valueEncoding contractABI compileEnv venomState
  words list arithmetic abiEncoderSharedMembersIndex abiEncoderSharedMembersInput
  abiEncoderOpenPrefix abiScratchMembersEntry abiScratchStatic abiScratchPrefix abiScratchCursor
  abiEncoderMembersDefs abiEncoderMembersStep abiEncoderTuple abiCanonicalWindows
  abiEncoderMemberCode abiEncoderArrayFrame abiScratchSubset pred_set valueEncodingProps

(* Rich observations from the generator's supplied static child endpoint. *)
Theorem abi_encoder_shared_member_static_output:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial actual ==>
  abi_encoder_shared_endpoint (ctx,func) (st,en,out,limit_st)
    (first,last,b,cap) (at,av,d+offset) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def, abi_encoder_spine_shared_post_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[] >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `p.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_shared_input_def] >>
  drule_all abi_encoder_spine_static_shared_transport >> simp[]
QED

Theorem abi_encoder_shared_member_dynamic_output:
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\ fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dp /\
  ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,src,ho,dp,st,en,out) initial actual ==>
  mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
  mem_word_at (d+ho) actual.vs_memory = n2w off /\
  mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
  abi_scratch_effect first last lo en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo en.cs_next_id) [(d,output_size)] initial actual /\
  (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual /\
  actual.vs_current_bb = en.cs_current_bb /\ actual.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~actual.vs_halted /\
  abi_decode_footprint_frame
    ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
      abi_decoder_child_scratch (abi_decoder_ids lo en.cs_next_id) b cap initial) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ops p len ce r u. _` mp_tac >>
  disch_then (qx_choose_then `child_ops` mp_tac) >>
  disch_then (qx_choose_then `p` mp_tac) >>
  disch_then (qx_choose_then `child_len` mp_tac) >>
  disch_then (qx_choose_then `ce` mp_tac) >>
  disch_then (qx_choose_then `r` mp_tac) >>
  disch_then (qx_choose_then `u` mp_tac) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >> gvs[] >>
  drule abi_encoder_shared_member_dynamic_saved >> strip_tac >>
  qpat_assum `abi_encoder_shared_member_dynamic_post _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_member_dynamic_post_def]) >>
  fs[abi_encoder_spine_shared_post_def, abi_encoder_spine_core_code_def] >> gvs[] >>
  `p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
    first <= p.cs_next_id /\ ce.cs_next_id <= last /\
    site < p.cs_next_id /\ st.cs_next_var <= p.cs_next_var /\
    st.cs_next_var <= ce.cs_next_var /\ lo <= p.cs_next_id /\
    site IN abi_decoder_ids lo en.cs_next_id /\ site IN abi_decoder_ids first last` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
     simp_tac bool_ss [] >> decide_tac) >>
  `eval_operand dst initial = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var dst /\ d+output_size < dimword (:256)` by
    fs[abi_encoder_shared_input_def] >>
  `d+ho < dimword (:256) /\ d <= d+ho /\ d+ho+32 <= d+output_size /\
    d <= d+off /\ d+off+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  `abi_decoder_operand_live ce.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  `abi_decoder_address_frame st.cs_next_var initial r` by asm_rewrite_tac [] >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_encoder_shared_input_def] >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap r)` by
    (drule_all abi_encoder_address_scratch_disjoint >> simp[]) >>
  qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encoder_shared_member_dynamic_post _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encoder_shared_member_dynamic_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` kall_tac >>
  `ce.cs_next_id <= en.cs_next_id` by decide_tac >>
  drule_all (SRULE [] (Q.INST [`hi` |-> `en.cs_next_id`, `next` |-> `st.cs_next_var`]
    abi_encoder_spine_dynamic_shared_effects)) >> strip_tac >>
  drule_all abi_encoder_spine_dynamic_shared_sim >>
  disch_then assume_tac >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  `eval_operand child_len u = SOME (n2w (LENGTH (enc at av)))` by
    fs[abi_encoder_shared_endpoint_def] >>
  drule_all abi_encoder_spine_cursor_post >> disch_tac >>
  drule_all (SRULE [] (Q.INST [`hi` |-> `en.cs_next_id`, `next` |-> `st.cs_next_var`]
    abi_scratch_child_effect)) >> strip_tac >>
  `d+ho+32 <= d+off` by decide_tac >>
  drule_all abi_encoder_shared_suffix_observations >> strip_tac >>
  asm_rewrite_tac []
QED

(* Tuple/cursor transport from supplied rich static child observations. *)
Theorem abi_encoder_shared_members_static_endpoint:
  compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_shared_input (ei,ty,av) (st,elem_src,dst) (sb+so,mem_sz)
    (d,output_size) (first,last,b,cap) initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_encoder_spine_shared_post (ctx,func) (ty,av,sb+so,mem_sz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_encoder_shared_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_shared_endpoint (ctx,func) (st,end_st,out,limit_st)
    (first,last,b,cap) (ty,av,d+ho) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_shared_members_inv_layout)) >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  `ho+LENGTH (enc ty av) <= output_size /\ first <= st.cs_next_id` by decide_tac >>
  drule_all abi_encoder_shared_member_static_output >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st (d+ho) (LENGTH (enc ty av)) b cap initial actual` by
    (drule abi_encoder_shared_endpoint_scratch >> simp[]) >>
  `abi_decode_footprint_frame
    ((d+ho,LENGTH (enc ty av))::abi_decoder_child_scratch
      (abi_decoder_ids first last) b cap initial) initial actual` by
    (drule_all abi_scratch_effect_frame >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_encoder_shared_input_def] >>
  drule abi_encoder_shared_endpoint_bytes >> disch_tac >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch
    (abi_decoder_ids first last) b cap initial`,
    `heads` |-> `ho:num`, `tails` |-> `LENGTH (FLAT (abi_tuple_tails pre pvs))`]
    abi_scratch_tuple_static_step) >>
  impl_tac >- gvs[abi_encoder_shared_endpoint_bytes, Excl "enc_def"] >> disch_tac >>
  `abi_footprint_disjoint (d+ho) (LENGTH (enc ty av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`,`output_size`] >>
     gvs[Excl "enc_def"] >> decide_tac) >>
  `abi_encoder_cursor active dyn_ptr site slot first lo st
    (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) actual` by
    (reverse (Cases_on `active`) >- simp[abi_encoder_cursor_def] >>
     mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`, `owned_lo` |-> `st.cs_next_id`,
       `owned_hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`, `sz` |-> `LENGTH (enc ty av)`,
       `d` |-> `d+ho`]
       abi_scratch_cursor_protected) >>
     impl_tac >- (fs[abi_encoder_cursor_def, abi_encoder_shared_input_def] >> decide_tac) >> simp[]) >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    gvs[abi_encoder_open_prefix_tail_advance, Excl "enc_def"] >>
  `abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d+ho`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `LENGTH (enc ty av)`] >>
     gvs[Excl "enc_def"] >> decide_tac) >>
  `~actual.vs_halted /\ actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts` by fs[abi_encoder_shared_endpoint_def] >>
  drule_all (Q.INST [`dyn` |-> `F`] abi_encoder_shared_members_after_child) >> strip_tac >>
  asm_rewrite_tac []
QED

Theorem abi_encoder_shared_members_static_exit:
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
  ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\ hi <= last /\
  ce.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_encoder_spine_shared_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r u ==>
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_shared_members_inv ((ei,az,mz,F)::infos) (ty::tys) (av::avs) pre pvs
    active dp site slot first last lo p limit_st src dst sb so ho d hl sz b cap r /\
    lo <= p.cs_next_id /\ fresh_vars_wrt limit_st r` by
    (PairCases_on `target` >> fs[abi_encoder_shared_members_index_def, abi_encoder_shared_members_inv_def]) >>
  drule_all abi_encoder_shared_members_static_endpoint >> strip_tac >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_shared_members_inv_layout)) >> strip_tac >>
  `ho+LENGTH (enc ty av) <= sz` by decide_tac >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] r u` by
    (irule abi_encoder_spine_shared_registered_window >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `alloca_inv r ==> alloca_inv u` by fs[abi_encoder_shared_endpoint_def] >>
  `abi_encoder_extend_sim ctx func r u` by fs[abi_encoder_shared_endpoint_def] >>
  `p.cs_next_var <= ce.cs_next_var` by
    (drule abi_encoder_child_bounds >> simp[]) >>
  `abi_decoder_address_frame p.cs_next_var r r` by simp[abi_decoder_address_frame_def] >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] r r` by
    simp[abi_encoder_registered_effect_refl] >>
  `abi_encoder_extend_sim ctx func r r` by simp[abi_encoder_extend_sim_refl] >>
  irule abi_encoder_shared_members_index_advance >>
  asm_rewrite_tac [] >> qexistsl_tac [`F`, `ei`, `p`, `r`, `r`, `p`] >>
  gvs[Excl "enc_def"]
QED

Theorem abi_encoder_shared_members_dynamic_endpoint:
  compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  abi_encode_child_prefix dst ho dyn_ptr st = (ops,prepared) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_shared_input (ei,ty,av) (st,elem_src,dst) (sb+so,mem_sz)
    (d,output_size) (first,last,b,cap) initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_spine_child_output
    (abi_encoder_shared_member_dynamic_post (ctx,func) (ty,av,sb+so,mem_sz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dyn_ptr,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_encoder_shared_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo end_st.cs_next_id) [(d,output_size)] initial actual /\
  (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_encoder_shared_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_encoder_shared_members_inv_layout)) >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= output_size /\
    mload slot initial = n2w off` by fs[] >>
  drule_all abi_encoder_shared_member_dynamic_output >> strip_tac >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
     fs[abi_encoder_shared_input_def, abi_decoder_ids_def, SUBSET_DEF] >> decide_tac) >>
  `abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory` by
    (irule abi_scratch_tuple_dynamic_step >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial`,
       `initial`, `output_size`] >> gvs[Excl "enc_def"]) >>
  `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) =
    LENGTH (FLAT (abi_tuple_tails pre pvs)) + LENGTH (enc ty av)` by
    simp[abi_encoder_open_prefix_tail_advance] >>
  qpat_assum `mem_word_at slot actual.vs_memory = _`
    (assume_tac o PURE_REWRITE_RULE [mem_word_at_eq_mload]) >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`] abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC, LESS_EQ_REFL] >> disch_tac >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  drule_all (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_encoder_shared_members_after_child) >>
  strip_tac >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_members_dynamic_exit:
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
  ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\ hi <= last /\
  ce.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_spine_child_output
    (abi_encoder_shared_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r u ==>
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_shared_members_inv ((ei,az,mz,T)::infos) (ty::tys) (av::avs) pre pvs
    active dp site slot first last lo p limit_st src dst sb so ho d hl sz b cap r /\
    lo <= p.cs_next_id /\ fresh_vars_wrt limit_st r` by
    (PairCases_on `target` >> fs[abi_encoder_shared_members_index_def, abi_encoder_shared_members_inv_def]) >>
  drule_all abi_encoder_shared_members_dynamic_endpoint >> strip_tac >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] r u` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[abi_decoder_ids_def, SUBSET_DEF] >> decide_tac) >>
  `p.cs_next_var <= ce.cs_next_var` by
    (drule abi_encoder_child_bounds >> simp[]) >>
  `abi_decoder_address_frame p.cs_next_var r r` by simp[abi_decoder_address_frame_def] >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] r r` by
    simp[abi_encoder_registered_effect_refl] >>
  `abi_encoder_extend_sim ctx func r r` by simp[abi_encoder_extend_sim_refl] >>
  irule abi_encoder_shared_members_index_advance >>
  asm_rewrite_tac [] >> qexistsl_tac [`T`, `ei`, `p`, `r`, `r`, `p`] >>
  gvs[Excl "enc_def"]
QED
