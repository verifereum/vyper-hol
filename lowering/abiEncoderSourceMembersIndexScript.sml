(* Fixed-origin ghost ledger for the source interpretation of MemberSpine. *)
Theory abiEncoderSourceMembersIndex
Ancestors
  abiEncoderMembersStep abiEncoderMembersContract abiEncoderMembersDefs
  abiEncoderMemberSpine abiEncoderCorrect abiEncoderInput abiEncoderTuple
  abiDecoderEffect abiDecoderLoop compileEnv venomState list arithmetic

Definition abi_encoder_source_members_index_def:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
      (first,last,lo,hi,b,cap,limit_st)
      (active,dp,site,slot,src,dst,sb,d,hl,sz)
      (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) (tys,avs,pre,pvs) s <=>
    EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos /\
    abi_encoder_members_inv infos tys avs pre pvs active dp site slot first last lo
      st limit_st src dst sb so ho d hl sz b cap s /\
    pre++tys = all_tys /\ pvs++avs = all_avs /\
    so+abi_encoder_member_span infos = end_so /\
    ho+SUM (MAP (\(_,az,_,_). az) infos) = end_ho /\
    origin.cs_next_var <= st.cs_next_var /\
    abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
    abi_decode_sim ctx func initial s
End

Theorem abi_encoder_source_members_index_initial:
  EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos /\
  abi_encoder_members_inv infos tys avs pre pvs active dp site slot first last lo
    st limit_st src dst sb so ho d hl sz b cap initial ==>
  abi_encoder_source_members_index (ctx,func) (st,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (pre++tys,pvs++avs,so+abi_encoder_member_span infos,ho+SUM (MAP (\(_,az,_,_). az) infos))
    infos (st,so,ho) (tys,avs,pre,pvs) initial
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial` by
    fs[abi_encoder_members_inv_def] >>
  simp[abi_encoder_source_members_index_def, abi_decoder_effect_refl, abi_decode_sim_refl]
QED

Theorem abi_encoder_source_members_index_source:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (st,so,ho) x s ==>
  (?sw. eval_operand src s = SOME sw) /\ fresh_vars_wrt limit_st s
Proof
  PairCases_on `target` >> PairCases_on `x` >>
  simp_tac bool_ss [abi_encoder_source_members_index_def] >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  asm_rewrite_tac [] >> qexists_tac `n2w sb` >> asm_rewrite_tac []
QED

Theorem abi_encoder_source_members_index_empty:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_encoder_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
    st limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s
Proof
  PairCases_on `x` >>
  simp_tac bool_ss [abi_encoder_source_members_index_def] >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_members_empty_types >> strip_tac >>
  gvs[abi_encoder_member_span_def, Excl "enc_def"]
QED

Theorem abi_encoder_source_members_index_advance:
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dp site slot
    first last lo ce limit_st src dst sb (so+mz) (ho+az) d hl sz b cap u /\
  abi_decoder_address_frame st.cs_next_var s r /\ fresh_vars_wrt limit_st r /\
  abi_decode_sim ctx func s r /\
  abi_decoder_effect first last lo ce.cs_next_id prepared.cs_next_var
    limit_st d sz b cap r u /\ abi_decode_sim ctx func r u /\
  st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= ce.cs_next_var /\
  ce.cs_next_id <= hi ==>
  abi_encoder_source_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_source_members_index_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_budget first last b cap s` by fs[abi_encoder_members_inv_def] >>
  `origin.cs_next_var <= prepared.cs_next_var /\ origin.cs_next_var <= ce.cs_next_var`
    by decide_tac >>
  drule_all abi_encoder_members_origin_transport >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [EVERY_DEF, abi_encoder_member_span_def,
    MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC, GSYM APPEND_ASSOC, APPEND]) >>
  asm_simp_tac bool_ss [abi_encoder_member_span_def, ADD_ASSOC, GSYM APPEND_ASSOC, APPEND]
QED
