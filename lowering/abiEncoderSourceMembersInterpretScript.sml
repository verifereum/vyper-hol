(* Branch-indexed core contracts for the common list generator. *)
Theory abiEncoderSourceMembersInterpret
Ancestors
  abiEncoderSourceMembersEntry abiEncoderMemberSourceContract abiEncoderMemberSpine
  abiDecoderLoop pair abiEncoderSourceMembersIndex abiEncoderTuple abiEncoderInput
  abiEncoder abiEncoderMembersContract abiDecoderEffect compileEnv venomState list arithmetic

Definition abi_encoder_source_members_child_pre_def:
  abi_encoder_source_members_child_pre resources (dyn,value,cursor) c s <=>
    if dyn then abi_encoder_member_dynamic_pre value resources cursor c s
    else abi_encoder_member_core_pre value resources c s
End

Definition abi_encoder_source_members_child_post_def:
  abi_encoder_source_members_child_post (ctx,func) resources (dyn,value,cursor) c s t <=>
    if dyn then abi_encoder_member_dynamic_post (ctx,func) value resources cursor c s t
    else abi_encoder_member_core_post (ctx,func) value resources c s t
End
Theorem abi_encoder_source_members_child_dispatch:
  abi_encoder_source_members_child_pre resources (T,value,cursor) =
    abi_encoder_member_dynamic_pre value resources cursor /\
  abi_encoder_source_members_child_pre resources (F,value,cursor) =
    abi_encoder_member_core_pre value resources /\
  abi_encoder_source_members_child_post (ctx,func) resources (T,value,cursor) =
    abi_encoder_member_dynamic_post (ctx,func) value resources cursor /\
  abi_encoder_source_members_child_post (ctx,func) resources (F,value,cursor) =
    abi_encoder_member_core_post (ctx,func) value resources
Proof
  simp[FUN_EQ_THM, abi_encoder_source_members_child_pre_def,
    abi_encoder_source_members_child_post_def]
QED

Theorem abi_encoder_source_members_child_run:
  !y c r. abi_encoder_spine_core_code func c /\
    abi_encoder_source_members_child_pre resources y c r ==>
    ?u. abi_decode_sim ctx func r u /\
      abi_encoder_source_members_child_post (ctx,func) resources y c r u
Proof
  rpt gen_tac >> PairCases_on `y` >> Cases_on `y0` >>
  simp_tac bool_ss [abi_encoder_source_members_child_pre_def,
    abi_encoder_source_members_child_post_def, pairTheory.UNCURRY_DEF] >>
  rpt strip_tac
  >- (irule abi_encoder_member_source_dynamic_run >> asm_rewrite_tac []) >>
  irule abi_encoder_member_source_core_run >> asm_rewrite_tac []
QED

Definition abi_encoder_source_members_entry_def:
  abi_encoder_source_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y <=>
  ?ty tys av avs pre pvs.
    x = (ty::tys,av::avs,pre,pvs) /\
    abi_encoder_source_members_index (ctx,func) (origin,initial)
      (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
      target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
    abi_encoder_buffer_pre ei ty av p elem_src dst (sb+so) mz d sz b cap r /\
    compile_abi_encode_child dst elem_src ei dyn ho dp p = (len,ce) /\
    fn_has_code p ce func /\
    (p.cs_blocks = ce.cs_blocks \/
      !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\
    ce.cs_next_var <= limit_st.cs_next_var /\
    (if dyn then ?ops prepared.
       abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
       y = (T,(ty,av,sb+so,mz,d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))),
         (FST ops,FST (SND ops),dp,d+ho,hl+LENGTH (FLAT (abi_tuple_tails pre pvs)),slot,site))
     else y = (F,(ty,av,sb+so,mz,d+ho),(dst,dst,dp,d+ho,0,slot,site)))
End

Theorem abi_encoder_source_members_entry_input:
  abi_encoder_source_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_source_members_child_pre (first,last,b,cap,limit_st) y)
    (abi_encoder_source_members_child_post (ctx,func) (first,last,b,cap,limit_st) y)
    (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r
Proof
  simp_tac bool_ss [abi_encoder_source_members_entry_def] >>
  ntac 6 (disch_then (CHOOSE_THEN mp_tac)) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `dyn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      simp_tac bool_ss [] >> ntac 2 (disch_then (CHOOSE_THEN mp_tac)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `y = _` SUBST1_TAC >>
      simp_tac bool_ss [abi_encoder_source_members_child_dispatch] >>
      drule_all (SRULE [] (Q.INST
        [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
        abi_encoder_source_members_dynamic_request)) >> simp[]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp_tac bool_ss [] >>
  disch_then SUBST1_TAC >>
  simp_tac bool_ss [abi_encoder_source_members_child_dispatch] >>
  drule_all abi_encoder_source_members_static_request >> simp[]
QED

Theorem abi_encoder_source_members_entry_exit:
  abi_encoder_source_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y /\
  abi_encoder_spine_child_output
    (abi_encoder_source_members_child_post (ctx,func) (first,last,b,cap,limit_st) y)
    (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r u ==>
  ?x'. abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) x' u
Proof
  simp_tac bool_ss [abi_encoder_source_members_entry_def, PULL_EXISTS] >>
  rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `dyn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      simp_tac bool_ss [] >> ntac 2 (disch_then (CHOOSE_THEN mp_tac)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `y = _` SUBST_ALL_TAC >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_encoder_source_members_child_dispatch]) >>
      drule_all (SRULE [] (Q.INST
        [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
        abi_encoder_source_members_dynamic_exit)) >>
      disch_then assume_tac >> goal_assum (drule_at Any)) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp_tac bool_ss [] >>
  disch_then SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_encoder_source_members_child_dispatch]) >>
  drule_all abi_encoder_source_members_static_exit >>
  disch_then assume_tac >> goal_assum (drule_at Any)
QED

Theorem abi_encoder_source_members_entry_prepare:
  hi <= last /\
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) x s /\
  abi_encoder_spine_cons_layout func limit_st hi (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  abi_encoder_member_phase_raw st p s r ==>
  ?y. abi_encoder_source_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_source_members_index_cons_shape >> strip_tac >>
  qpat_x_assum `x = _` SUBST_ALL_TAC >>
  drule_all abi_encoder_spine_cons_layout_bound >> strip_tac >>
  drule_all abi_encoder_source_members_index_prepare >> strip_tac >>
  qpat_assum `abi_encoder_spine_cons_layout _ _ hi _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_encoder_spine_cons_layout_def]) >>
  qpat_assum `abi_encoder_spine_code _ _ hi _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_code_def]) >>
  `ce.cs_next_id <= hi /\ ce.cs_next_id <= last /\
    ce.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  simp_tac bool_ss [abi_encoder_source_members_entry_def] >>
  Cases_on `dyn`
  >- (Cases_on `abi_encode_child_prefix dst ho dp p` >>
      rename1 `abi_encode_child_prefix dst ho dp p = (ops,prepared)` >>
      qexists_tac `(T,(ty,av,sb+so,mz,d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))),
        (FST ops,FST (SND ops),dp,d+ho,hl+LENGTH (FLAT (abi_tuple_tails pre pvs)),slot,site))` >>
      qexistsl_tac [`ty`,`tys`,`av`,`avs`,`pre`,`pvs`] >>
      asm_rewrite_tac [] >> qexistsl_tac [`ops`,`prepared`] >> asm_rewrite_tac []) >>
  qexists_tac `(F,(ty,av,sb+so,mz,d+ho),(dst,dst,dp,d+ho,0,slot,site))` >>
  qexistsl_tac [`ty`,`tys`,`av`,`avs`,`pre`,`pvs`] >> asm_rewrite_tac []
QED

Theorem abi_encoder_source_members_empty_post:
  abi_encoder_spine_code func limit_st hi (dst,src,dp) [] (st,so,ho) (out,en) /\
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_encoder_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
    en limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_source_members_index_empty >> strip_tac >>
  qpat_assum `abi_encoder_spine_code _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_code_def]) >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[]
QED

Theorem abi_encoder_source_members_generate:
  hi <= last /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s ==>
  ?t. abi_encoder_member_spine (\c r u. abi_decode_sim ctx func r u)
      (dst,src,dp) infos (st,so,ho) (out,en) s t /\
    abi_encoder_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (SRULE [] (Q.SPECL [
    `abi_encoder_source_members_child_pre (first,last,b,cap,limit_st)`,
    `abi_encoder_source_members_child_post (ctx,func) (first,last,b,cap,limit_st)`,
    `\c r u. abi_decode_sim ctx func r u`,
    `\(out,en) t.
      abi_encoder_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
        en limit_st src dst sb end_so end_ho d hl sz b cap t /\
      abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
      abi_decode_sim ctx func initial t`, `hi`] (  Q.ISPECL [
    `abi_encoder_source_members_index (ctx,func) (origin,initial)
      (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
      (all_tys,all_avs,end_so,end_ho)`,
    `\i (st:compile_state,so,ho) x (s:venom_state).
      abi_encoder_source_members_entry (ctx,func) (origin,initial)
        (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
        (all_tys,all_avs,end_so,end_ho) i (st,so,ho) x s`]
    (Q.GENL [`Inv`,`Entry`,`child_pre`,`child_post`,`core_run`,`Post`,`last`]
      abi_encoder_member_spine_generate)))) >>
  simp_tac bool_ss [] >> impl_tac
  >- (conj_tac >- MATCH_ACCEPT_TAC abi_encoder_source_members_child_run >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_encoder_source_members_index_source) >>
      conj_tac
      >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          drule_all abi_encoder_source_members_entry_prepare >> simp[]) >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_encoder_source_members_entry_input) >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_encoder_source_members_entry_exit) >>
      rpt gen_tac >> MATCH_ACCEPT_TAC abi_encoder_source_members_empty_post) >>
  disch_then (qspecl_then [`infos`,`st`,`so`,`ho`,`out`,`en`,`x`,`s`] mp_tac) >>
  asm_rewrite_tac []
QED
