(* Universal transport at the shared generator's physical source-ADD endpoint. *)
Theory abiScratchMembersEntry
Ancestors
  abiScratchMembersIndex abiEncoderMemberPhaseExec abiEncoderMemberPhaseRaw
  abiScratchMemberInterpret abiScratchMembersEndpoint abiEncoderMemberCode
  abiEncoderMemberSpine abiScratchMembers abiScratchAddress abiScratchEffect
  abiEncoderMembersDefs abiEncoderInput abiDecoderLoop abiDecoderDynamicLoopSetup
  compileEnv venomState list arithmetic

Theorem abi_scratch_members_index_prepare:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_encoder_spine_cons_layout func limit_st last (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  hi <= last /\ abi_encoder_member_phase_raw st p s r ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  abi_decoder_address_frame st.cs_next_var s r /\ abi_decode_sim ctx func s r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def, abi_encoder_spine_cons_layout_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_members_prepare_raw_transport >> strip_tac >>
  `abi_decoder_budget first last b cap s /\ first <= lo /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_scratch_members_inv_def] >>
  `fresh_vars_wrt limit_st r` by fs[abi_scratch_members_inv_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `origin.cs_next_var <= p.cs_next_var` by decide_tac >>
  `abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap s r` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap s r` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`hi`,`lo:num`,`st.cs_next_var`,`sz:num`] >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial r` by
    (irule abi_scratch_effect_trans >> asm_rewrite_tac [] >> qexists_tac `s` >> asm_rewrite_tac []) >>
  `abi_decode_sim ctx func initial r` by
    (irule abi_decode_sim_trans >> qexists_tac `s` >> asm_rewrite_tac []) >>
  asm_rewrite_tac [] >> decide_tac
QED

Theorem abi_scratch_members_static_request:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,F)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei F ho dp p = (len,ce) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_core_pre (ty,av,sb+so,mz,d+ho) (first,last,b,cap,limit_st))
    (abi_scratch_member_core_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_scratch_members_inv_layout)) >> strip_tac >>
  `ho+LENGTH (enc ty av) <= sz` by decide_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `first <= p.cs_next_id` by decide_tac >>
  drule_all abi_scratch_member_static_input >> simp[]
QED

Theorem abi_scratch_members_dynamic_request:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,T)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei T ho dp p = (len,ce) /\
  abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_dynamic_pre (ty,av,sb+so,mz,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (abi_scratch_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`] abi_scratch_members_inv_layout)) >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `active` by fs[EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= sz` by decide_tac >>
  `abi_decoder_operand_live p.cs_next_var dp /\
    eval_operand dp r = SOME (n2w slot) /\ mload slot r = n2w off /\
    first <= site /\ site < p.cs_next_id /\ FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    (qpat_assum `active` (fn ath =>
       qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
         (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def,ath])) >>
     asm_rewrite_tac []) >>
  drule_all abi_scratch_member_dynamic_input >> simp[]
QED

Theorem abi_scratch_members_static_exit:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,F)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei F ho dp p = (len,ce) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\ hi <= last /\
  ce.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_scratch_member_core_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r u ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_members_inv ((ei,az,mz,F)::infos) (ty::tys) (av::avs) pre pvs
    active dp site slot first last lo p limit_st src dst sb so ho d hl sz b cap r /\
    fresh_vars_wrt limit_st r` by
    (PairCases_on `target` >> fs[abi_scratch_members_index_def, abi_scratch_members_inv_def]) >>
  drule_all abi_scratch_members_static_endpoint >> strip_tac >>
  `p.cs_next_var <= ce.cs_next_var` by
    (drule abi_encoder_child_bounds >> simp[]) >>
  `abi_decoder_address_frame p.cs_next_var r r` by simp[abi_decoder_address_frame_def] >>
  `abi_decode_sim ctx func r r` by simp[abi_decode_sim_refl] >>
  irule abi_scratch_members_index_advance >>
  asm_rewrite_tac [] >> qexistsl_tac [`F`, `ei`, `p`, `r`, `r`, `p`] >>
  asm_rewrite_tac [] >> decide_tac
QED

Theorem abi_scratch_members_dynamic_exit:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,T)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
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
    (abi_scratch_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r u ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_members_inv ((ei,az,mz,T)::infos) (ty::tys) (av::avs) pre pvs
    active dp site slot first last lo p limit_st src dst sb so ho d hl sz b cap r /\
    fresh_vars_wrt limit_st r` by
    (PairCases_on `target` >> fs[abi_scratch_members_index_def, abi_scratch_members_inv_def]) >>
  drule_all abi_scratch_members_dynamic_endpoint >> strip_tac >>
  `p.cs_next_var <= ce.cs_next_var` by
    (drule abi_encoder_child_bounds >> simp[]) >>
  `abi_decoder_address_frame p.cs_next_var r r` by simp[abi_decoder_address_frame_def] >>
  `abi_decode_sim ctx func r r` by simp[abi_decode_sim_refl] >>
  irule abi_scratch_members_index_advance >>
  asm_rewrite_tac [] >> qexistsl_tac [`T`, `ei`, `p`, `r`, `r`, `p`] >>
  asm_rewrite_tac [] >> decide_tac
QED
