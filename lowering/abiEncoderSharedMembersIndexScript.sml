(* Immutable origin for the open-source, rich member interpretation. *)
Theory abiEncoderSharedMembersIndex
Ancestors
  abiEncoderSharedMembersInput abiEncoderSharedMemberContract abiEncoderSharedContract
  abiEncoderMembersDefs abiEncoderTuple abiEncoderOpenInput abiEncoderInput
  abiEncoderExtendSim abiEncoderRegisteredEffect abiScratchEffect abiScratchDecoderLoopControl
  abiScratchEncoderContract abiScratchAddress abiEncoderMemberSpine
  abiDecoderAllocation abiDecoderReentry compileEnv venomState list arithmetic

Definition abi_encoder_shared_members_inv_def:
  abi_encoder_shared_members_inv infos tys avs pre pvs active dp site slot first last lo st limit_st
    src dst sb so ho d hl sz b cap s <=>
    abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s /\
    LIST_REL abi_encoder_structural_valid (pre++tys) (pvs++avs) /\
    LENGTH pre = LENGTH pvs /\ hl = head_lengths (pre++tys) 0 /\
    ho = SUM (MAP abi_member_head_size pre) /\
    LENGTH (enc (Tuple (pre++tys)) (ListV (pvs++avs))) <= sz /\
    abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
    abi_encoder_cursor active dp site slot first lo st
      (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) s /\
    (active \/ EVERY (\(_,_,_,dyn). ~dyn) infos) /\
    abi_decoder_budget first last b cap s /\ first <= lo /\ lo <= st.cs_next_id /\
    st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_shared_members_index_def:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
      (first,last,lo,hi,b,cap,limit_st)
      (active,dp,site,slot,src,dst,sb,d,hl,sz)
      (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) (tys,avs,pre,pvs) s <=>
    EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
    abi_encoder_shared_members_inv infos tys avs pre pvs active dp site slot first last lo
      st limit_st src dst sb so ho d hl sz b cap s /\
    pre++tys = all_tys /\ pvs++avs = all_avs /\
    so+abi_encoder_member_span infos = end_so /\
    ho+SUM (MAP (\(_,az,_,_). az) infos) = end_ho /\
    origin.cs_next_var <= st.cs_next_var /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial s /\
    (alloca_inv initial ==> alloca_inv s) /\
    abi_encoder_extend_sim ctx func initial s
End

Theorem abi_encoder_shared_members_index_initial:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
  abi_encoder_shared_members_inv infos tys avs pre pvs active dp site slot first last lo
    st limit_st src dst sb so ho d hl sz b cap initial ==>
  abi_encoder_shared_members_index (ctx,func) (st,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (pre++tys,pvs++avs,so+abi_encoder_member_span infos,ho+SUM (MAP (\(_,az,_,_). az) infos))
    infos (st,so,ho) (tys,avs,pre,pvs) initial
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial` by
    fs[abi_encoder_shared_members_inv_def] >>
  simp[abi_encoder_shared_members_index_def, abi_scratch_effect_refl,
    abi_encoder_registered_effect_refl, abi_encoder_extend_sim_refl]
QED

Theorem abi_encoder_shared_members_index_source:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (st,so,ho) x s ==>
  (?sw. eval_operand src s = SOME sw) /\ fresh_vars_wrt limit_st s
Proof
  PairCases_on `target` >> PairCases_on `x` >>
  simp_tac bool_ss [abi_encoder_shared_members_index_def] >> strip_tac >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  qpat_assum `abi_encoder_shared_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_pre_def]) >>
  asm_rewrite_tac [] >> qexists_tac `n2w sb` >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_members_index_empty:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_encoder_shared_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
    st limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial s /\
  (alloca_inv initial ==> alloca_inv s) /\ abi_encoder_extend_sim ctx func initial s
Proof
  PairCases_on `x` >>
  simp_tac bool_ss [abi_encoder_shared_members_index_def] >> strip_tac >>
  `x0 = [] /\ x1 = []` by
    (qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
     drule abi_encoder_shared_members_pre_empty >> simp[]) >>
  gvs[abi_encoder_member_span_def, Excl "enc_def"]
QED

Theorem abi_encoder_shared_members_inv_layout:
  abi_encoder_shared_members_inv ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dp site slot first last lo st limit_st
    src dst sb so ho d hl sz b cap s ==>
  abi_encoder_structural_valid ty av /\ LIST_REL abi_encoder_structural_valid tys avs /\
  az = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  ho = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  SUM (MAP2 abi_member_tail_size pre pvs) = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  ho+az <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs) <= sz /\
  (~dyn ==> ho+LENGTH (enc ty av) <= hl) /\
  (dyn ==> ho+32 <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs)+LENGTH (enc ty av) <= sz)
Proof
  simp_tac bool_ss [abi_encoder_shared_members_inv_def] >> strip_tac >>
  drule abi_encoder_shared_members_pre_cons >> strip_tac >>
  drule_all abi_encoder_open_members_layout >> strip_tac >>
  qpat_assum `ho = SUM _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_members_after_child:
  abi_encoder_shared_members_inv ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dp site slot first last lo st limit_st
    src dst sb so ho d hl sz b cap initial /\
  abi_scratch_effect first last lo en.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual /\
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory /\
  abi_encoder_cursor active dp site slot first lo en
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual /\
  st.cs_next_var <= en.cs_next_var /\ st.cs_next_id <= en.cs_next_id /\
  en.cs_next_id <= last /\ en.cs_next_var <= limit_st.cs_next_var /\
  ~actual.vs_halted /\ actual.vs_current_bb = en.cs_current_bb /\
  actual.vs_inst_idx = LENGTH en.cs_current_insts ==>
  abi_encoder_shared_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dp site slot first last lo
    en limit_st src dst sb (so+mz) (ho+az) d hl sz b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  `abi_encoder_shared_members_pre ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d sz first last b cap actual` by
    (drule_all abi_encoder_shared_members_pre_effect >> simp[]) >>
  `abi_encoder_shared_members_pre ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    en src dst sb so d sz first last b cap actual` by
    (irule abi_encoder_shared_members_pre_mono >> qexists_tac `st` >> asm_rewrite_tac []) >>
  qpat_assum `abi_encoder_shared_members_pre _ _ _ en _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o MATCH_MP abi_encoder_shared_members_pre_cons) >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `lo <= en.cs_next_id` by decide_tac >>
  pure_rewrite_tac [abi_encoder_shared_members_inv_def, GSYM APPEND_ASSOC, APPEND] >>
  asm_simp_tac bool_ss [LENGTH_APPEND, LENGTH, MAP_APPEND, SUM_APPEND, MAP, SUM, ADD_CLAUSES] >>
  qpat_x_assum `active \/ EVERY _ _` mp_tac >> simp_tac (srw_ss()) [] >>
  rpt strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_members_origin_transport:
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial s /\
  (alloca_inv initial ==> alloca_inv s) /\ abi_encoder_extend_sim ctx func initial s /\
  abi_decoder_address_frame st.cs_next_var s r /\ fresh_vars_wrt limit_st r /\
  abi_decoder_budget first last b cap s /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] s r /\
  (alloca_inv s ==> alloca_inv r) /\ abi_encoder_extend_sim ctx func s r /\
  abi_scratch_effect first last lo ce.cs_next_id prepared.cs_next_var
    limit_st d sz b cap r u /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] r u /\
  (alloca_inv r ==> alloca_inv u) /\ abi_encoder_extend_sim ctx func r u /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_var <= prepared.cs_next_var /\
  ce.cs_next_id <= hi /\ first <= lo /\ hi <= last ==>
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial u /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial u /\
  (alloca_inv initial ==> alloca_inv u) /\ abi_encoder_extend_sim ctx func initial u
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
  conj_tac
  >- (irule abi_encoder_registered_effect_trans >> qexists_tac `s` >> asm_rewrite_tac [] >>
      irule abi_encoder_registered_effect_trans >> qexists_tac `r` >> asm_rewrite_tac []) >>
  conj_tac >- metis_tac[] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `s` >> asm_rewrite_tac [] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `r` >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_members_index_advance:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_encoder_shared_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dp site slot
    first last lo ce limit_st src dst sb (so+mz) (ho+az) d hl sz b cap u /\
  abi_decoder_address_frame st.cs_next_var s r /\ fresh_vars_wrt limit_st r /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] s r /\
  (alloca_inv s ==> alloca_inv r) /\ abi_encoder_extend_sim ctx func s r /\
  abi_scratch_effect first last lo ce.cs_next_id prepared.cs_next_var
    limit_st d sz b cap r u /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] r u /\
  (alloca_inv r ==> alloca_inv u) /\ abi_encoder_extend_sim ctx func r u /\
  st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= ce.cs_next_var /\
  ce.cs_next_id <= hi /\ hi <= last ==>
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_shared_members_index_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_budget first last b cap s /\ first <= lo` by fs[abi_encoder_shared_members_inv_def] >>
  `origin.cs_next_var <= prepared.cs_next_var /\ origin.cs_next_var <= ce.cs_next_var`
    by decide_tac >>
  drule_all abi_encoder_shared_members_origin_transport >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [EVERY_DEF, abi_encoder_member_span_def,
    MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC, GSYM APPEND_ASSOC, APPEND]) >>
  asm_simp_tac bool_ss [abi_encoder_member_span_def, ADD_ASSOC, GSYM APPEND_ASSOC, APPEND]
QED
