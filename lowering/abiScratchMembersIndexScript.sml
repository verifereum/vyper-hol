(* Immutable origin and offset ledger for the physical scratch interpretation. *)
Theory abiScratchMembersIndex
Ancestors
  abiEncoderInput abiEncoderMembersDefs abiScratchMembers abiScratchMemberContract abiScratchAddress abiScratchEffect
  abiScratchDecoderLoopControl abiEncoderMemberSpine abiEncoderMembersContract
  abiDecoderEffect abiDecoderLoop compileEnv venomState list arithmetic

Definition abi_scratch_members_index_def:
  abi_scratch_members_index (ctx,func) (origin,initial)
      (first,last,lo,hi,b,cap,limit_st)
      (active,dp,site,slot,src,dst,sb,d,hl,sz)
      (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) (tys,avs,pre,pvs) s <=>
    EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
    abi_scratch_members_inv infos tys avs pre pvs active dp site slot first last lo
      st limit_st src dst sb so ho d hl sz b cap s /\
    pre++tys = all_tys /\ pvs++avs = all_avs /\
    so+abi_encoder_member_span infos = end_so /\
    ho+SUM (MAP (\(_,az,_,_). az) infos) = end_ho /\
    origin.cs_next_var <= st.cs_next_var /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
    abi_decode_sim ctx func initial s
End

Theorem abi_scratch_members_index_initial:
  EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  abi_scratch_members_inv infos tys avs pre pvs active dp site slot first last lo
    st limit_st src dst sb so ho d hl sz b cap initial ==>
  abi_scratch_members_index (ctx,func) (st,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (pre++tys,pvs++avs,so+abi_encoder_member_span infos,ho+SUM (MAP (\(_,az,_,_). az) infos))
    infos (st,so,ho) (tys,avs,pre,pvs) initial
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial` by
    fs[abi_scratch_members_inv_def] >>
  simp[abi_scratch_members_index_def, abi_scratch_effect_refl, abi_decode_sim_refl]
QED

Theorem abi_scratch_members_index_source:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (st,so,ho) x s ==>
  (?sw. eval_operand src s = SOME sw) /\ fresh_vars_wrt limit_st s
Proof
  PairCases_on `target` >> PairCases_on `x` >>
  simp_tac bool_ss [abi_scratch_members_index_def] >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  asm_rewrite_tac [] >> qexists_tac `n2w sb` >> asm_rewrite_tac []
QED

Theorem abi_scratch_members_index_empty:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
    st limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s
Proof
  PairCases_on `x` >>
  simp_tac bool_ss [abi_scratch_members_index_def] >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_empty_types >> strip_tac >>
  gvs[abi_encoder_member_span_def, Excl "enc_def"]
QED

Theorem abi_scratch_members_origin_transport:
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s /\
  abi_decoder_address_frame st.cs_next_var s r /\ fresh_vars_wrt limit_st r /\
  abi_decoder_budget first last b cap s /\ abi_decode_sim ctx func s r /\
  abi_scratch_effect first last lo ce.cs_next_id prepared.cs_next_var
    limit_st d sz b cap r u /\ abi_decode_sim ctx func r u /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_var <= prepared.cs_next_var /\
  ce.cs_next_id <= hi /\ first <= lo /\ hi <= last ==>
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial u /\
  abi_decode_sim ctx func initial u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap s r` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap s r` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`hi`,`lo:num`,`st.cs_next_var`,`sz:num`] >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap r u` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`ce.cs_next_id`,`lo:num`,`prepared.cs_next_var`,`sz:num`] >> simp[]) >>
  conj_tac
  >- (irule abi_scratch_effect_trans >> asm_rewrite_tac [] >> qexists_tac `s` >>
      asm_rewrite_tac [] >> irule abi_scratch_effect_trans >> asm_rewrite_tac [] >>
      qexists_tac `r` >> asm_rewrite_tac []) >>
  irule abi_decode_sim_trans >> qexists_tac `s` >> asm_rewrite_tac [] >>
  irule abi_decode_sim_trans >> qexists_tac `r` >> asm_rewrite_tac []
QED

Theorem abi_scratch_members_index_advance:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dp site slot
    first last lo ce limit_st src dst sb (so+mz) (ho+az) d hl sz b cap u /\
  abi_decoder_address_frame st.cs_next_var s r /\ fresh_vars_wrt limit_st r /\
  abi_decode_sim ctx func s r /\
  abi_scratch_effect first last lo ce.cs_next_id prepared.cs_next_var
    limit_st d sz b cap r u /\ abi_decode_sim ctx func r u /\
  st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= ce.cs_next_var /\
  ce.cs_next_id <= hi /\ hi <= last ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_budget first last b cap s /\ first <= lo` by fs[abi_scratch_members_inv_def] >>
  `origin.cs_next_var <= prepared.cs_next_var /\ origin.cs_next_var <= ce.cs_next_var`
    by decide_tac >>
  drule_all abi_scratch_members_origin_transport >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [EVERY_DEF, abi_encoder_member_span_def,
    MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC, GSYM APPEND_ASSOC, APPEND]) >>
  asm_simp_tac bool_ss [abi_encoder_member_span_def, ADD_ASSOC, GSYM APPEND_ASSOC, APPEND]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "scratch index has an admission, axiom or hypothesis"
  end) [abi_scratch_members_index_initial, abi_scratch_members_index_source,
    abi_scratch_members_index_empty, abi_scratch_members_origin_transport,
    abi_scratch_members_index_advance];
