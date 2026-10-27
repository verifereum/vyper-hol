(* Universal source-address transport for the indexed list interpretation.
   MemberSpine, not this theory, supplies the actual raw endpoint. *)
Theory abiEncoderSourceMembersEntry
Ancestors
  abiEncoderSourceMembersIndex abiEncoderMemberSourcePhase abiEncoderMemberPhaseRaw
  abiEncoderMemberSpine abiEncoderMembersContract abiEncoderMembersDefs
  abiEncoderMembersLayout abiEncoderMemberSourceInterpret abiEncoderMemberSourceContract
  abiEncoderMemberSourceAdapter
  abiDecoderEffect abiDecoderLoop compileEnv venomState list arithmetic

Theorem abi_encoder_source_members_index_prepare:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_encoder_spine_cons_layout func limit_st last (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  abi_encoder_member_phase_raw st p s r ==>
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_encoder_buffer_pre ei ty av p elem_src dst (sb+so) mz d sz b cap r /\
  abi_decoder_address_frame st.cs_next_var s r /\ abi_decode_sim ctx func s r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_source_members_index_def, abi_encoder_spine_cons_layout_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_members_prepare_raw_transport >> strip_tac >>
  `abi_decoder_budget first last b cap s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_members_inv_def] >>
  `fresh_vars_wrt limit_st r` by
    fs[abi_encoder_members_inv_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `origin.cs_next_var <= p.cs_next_var` by decide_tac >>
  `abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap s r` by
    (irule abi_decoder_address_effect >> asm_rewrite_tac [] >>
     qexists_tac `st.cs_next_var` >> asm_rewrite_tac []) >>
  `abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial r` by
    (irule abi_decoder_effect_trans >> qexists_tac `s` >> asm_rewrite_tac []) >>
  `abi_decode_sim ctx func initial r` by
    (irule abi_decode_sim_trans >> qexists_tac `s` >> asm_rewrite_tac []) >>
  asm_rewrite_tac [] >> decide_tac
QED

Theorem abi_encoder_source_members_static_request:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,F)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_encoder_buffer_pre ei ty av p elem_src dst (sb+so) mz d sz b cap r /\
  compile_abi_encode_child dst elem_src ei F ho dp p = (len,ce) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_member_core_pre (ty,av,sb+so,mz,d+ho) (first,last,b,cap,limit_st))
    (abi_encoder_member_core_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_source_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_members_inv_layout)) >> strip_tac >>
  `ho+LENGTH (enc ty av) <= sz` by decide_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  drule_all abi_encoder_member_source_static_input >> simp[]
QED

Theorem abi_encoder_source_members_dynamic_request:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,T)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_encoder_buffer_pre ei ty av p elem_src dst (sb+so) mz d sz b cap r /\
  compile_abi_encode_child dst elem_src ei T ho dp p = (len,ce) /\
  abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_member_dynamic_pre (ty,av,sb+so,mz,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (abi_encoder_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_source_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`] abi_encoder_members_inv_layout)) >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  `active` by fs[EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= sz` by decide_tac >>
  `abi_decoder_operand_live p.cs_next_var dp /\
    eval_operand dp r = SOME (n2w slot) /\ mload slot r = n2w off /\
    first <= site /\ site < p.cs_next_id /\ FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    (qpat_assum `active` (fn ath =>
       qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
         (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def,ath])) >>
     asm_rewrite_tac []) >>
  drule_all abi_encoder_member_source_dynamic_input >> simp[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "source entry has an admission, axiom or hypothesis"
  end) [abi_encoder_source_members_index_prepare, abi_encoder_source_members_static_request,
    abi_encoder_source_members_dynamic_request];
