(* Physical scratch interpretation of the single shared member generator. *)
Theory abiScratchMembersInterpret
Ancestors
  abiScratchMembersEntry abiScratchMemberContract abiEncoderMemberSpine abiEncoderMemberGuard
  abiEncoderChildCapability abiEncoderChildContext abiSiteEncoderContract
  abiEncoderAppend abiEncoderCounters
  abiDecoderLoop pair abiScratchMembersIndex abiScratchMembers abiEncoderTuple abiEncoderInput
  abiEncoder abiEncoderMembersContract abiScratchEffect compileEnv venomState list arithmetic

Definition abi_scratch_members_child_pre_def:
  abi_scratch_members_child_pre resources (dyn,value,cursor) c s <=>
    if dyn then abi_scratch_member_dynamic_pre value resources cursor c s
    else abi_scratch_member_core_pre value resources c s
End

Definition abi_scratch_members_child_post_def:
  abi_scratch_members_child_post (ctx,func) resources (dyn,value,cursor) c s t <=>
    if dyn then abi_scratch_member_dynamic_post (ctx,func) value resources cursor c s t
    else abi_scratch_member_core_post (ctx,func) value resources c s t
End

Theorem abi_scratch_members_child_dispatch:
  abi_scratch_members_child_pre resources (T,value,cursor) =
    abi_scratch_member_dynamic_pre value resources cursor /\
  abi_scratch_members_child_pre resources (F,value,cursor) =
    abi_scratch_member_core_pre value resources /\
  abi_scratch_members_child_post (ctx,func) resources (T,value,cursor) =
    abi_scratch_member_dynamic_post (ctx,func) value resources cursor /\
  abi_scratch_members_child_post (ctx,func) resources (F,value,cursor) =
    abi_scratch_member_core_post (ctx,func) value resources
Proof
  simp[FUN_EQ_THM, abi_scratch_members_child_pre_def, abi_scratch_members_child_post_def]
QED

Theorem abi_scratch_members_child_run:
  !y c r. abi_encoder_spine_core_code func c /\
    abi_scratch_members_child_pre resources y c r ==>
    ?u. abi_decode_sim ctx func r u /\
      abi_scratch_members_child_post (ctx,func) resources y c r u
Proof
  rpt gen_tac >> PairCases_on `y` >> Cases_on `y0` >>
  simp_tac bool_ss [abi_scratch_members_child_pre_def,
    abi_scratch_members_child_post_def, pairTheory.UNCURRY_DEF] >>
  rpt strip_tac
  >- (irule abi_scratch_member_dynamic_run >> asm_rewrite_tac []) >>
  irule abi_scratch_member_core_run >> asm_rewrite_tac []
QED

Definition abi_scratch_members_entry_def:
  abi_scratch_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y <=>
  ?ty tys av avs pre pvs.
    x = (ty::tys,av::avs,pre,pvs) /\
    abi_scratch_members_index (ctx,func) (origin,initial)
      (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
      target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
    abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
    compile_abi_encode_child dst elem_src ei dyn ho dp p = (len,ce) /\
    fn_has_code p ce func /\
    (p.cs_blocks = ce.cs_blocks \/
      !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\ hi <= last /\
    ce.cs_next_var <= limit_st.cs_next_var /\
    (if dyn then ?ops prepared.
       abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
       y = (T,(ty,av,sb+so,mz,d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))),
         (FST ops,FST (SND ops),dp,d+ho,hl+LENGTH (FLAT (abi_tuple_tails pre pvs)),slot,site))
     else y = (F,(ty,av,sb+so,mz,d+ho),(dst,dst,dp,d+ho,0,slot,site)))
End

Theorem abi_scratch_members_entry_input:
  abi_scratch_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_members_child_pre (first,last,b,cap,limit_st) y)
    (abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st) y)
    (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r
Proof
  simp_tac bool_ss [abi_scratch_members_entry_def] >>
  ntac 6 (disch_then (CHOOSE_THEN mp_tac)) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `dyn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      simp_tac bool_ss [] >> ntac 2 (disch_then (CHOOSE_THEN mp_tac)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `y = _` SUBST1_TAC >>
      simp_tac bool_ss [abi_scratch_members_child_dispatch] >>
      drule_all (SRULE [] (Q.INST
        [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
        abi_scratch_members_dynamic_request)) >> simp[]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp_tac bool_ss [] >>
  disch_then SUBST1_TAC >>
  simp_tac bool_ss [abi_scratch_members_child_dispatch] >>
  drule_all abi_scratch_members_static_request >> simp[]
QED

Theorem abi_scratch_members_entry_exit:
  abi_scratch_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y /\
  abi_encoder_spine_child_output
    (abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st) y)
    (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r u ==>
  ?x'. abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) x' u
Proof
  simp_tac bool_ss [abi_scratch_members_entry_def, PULL_EXISTS] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `dyn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      simp_tac bool_ss [] >> ntac 2 (disch_then (CHOOSE_THEN mp_tac)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `y = _` SUBST_ALL_TAC >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_scratch_members_child_dispatch]) >>
      drule_all (SRULE [] (Q.INST
        [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
        abi_scratch_members_dynamic_exit)) >>
      disch_then assume_tac >> goal_assum (drule_at Any)) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp_tac bool_ss [] >>
  disch_then SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_scratch_members_child_dispatch]) >>
  drule_all abi_scratch_members_static_exit >>
  disch_then assume_tac >> goal_assum (drule_at Any)
QED

Theorem abi_scratch_members_index_cons_shape:
  abi_scratch_members_index (ctx,func) (origin,initial)
    resources (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) x s ==>
  ?ty tys av avs pre pvs. x = (ty::tys,av::avs,pre,pvs)
Proof
  PairCases_on `resources` >> PairCases_on `target` >> PairCases_on `x` >>
  simp_tac bool_ss [abi_scratch_members_index_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  `LENGTH ((ei,az,mz,dyn)::infos) = LENGTH x0 /\ LENGTH x0 = LENGTH x1` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _`
       (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp_tac (srw_ss()) [abi_encoder_complex_input_iff, abi_encoder_tuple_type_def] >>
     rpt strip_tac >> gvs[]) >>
  Cases_on `x0` >- gvs[] >> Cases_on `x1` >- gvs[] >> simp[]
QED

Theorem abi_scratch_members_entry_prepare:
  hi <= last /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) x s /\
  abi_encoder_spine_cons_layout func limit_st hi (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  abi_encoder_member_phase_raw st p s r ==>
  ?y. abi_scratch_members_entry (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_members_index_cons_shape >> strip_tac >>
  qpat_x_assum `x = _` SUBST_ALL_TAC >>
  drule_all abi_encoder_spine_cons_layout_bound >> strip_tac >>
  drule_all abi_scratch_members_index_prepare >> strip_tac >>
  qpat_assum `abi_encoder_spine_cons_layout _ _ hi _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_encoder_spine_cons_layout_def]) >>
  qpat_assum `abi_encoder_spine_code _ _ hi _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_code_def]) >>
  `ce.cs_next_id <= hi /\ ce.cs_next_id <= last /\
    ce.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  simp_tac bool_ss [abi_scratch_members_entry_def] >>
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

Theorem abi_scratch_members_empty_post:
  abi_encoder_spine_code func limit_st hi (dst,src,dp) [] (st,so,ho) (out,en) /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
    en limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_members_index_empty >> strip_tac >>
  qpat_assum `abi_encoder_spine_code _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_code_def]) >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[]
QED


(* The runtime invariant does not advance the compiler continuation during
   address preparation.  This separate ledger applies only at loop entries. *)
Definition abi_site_members_scoped_def:
  abi_site_members_scoped guard (out0,end0) world origin resources
    (active,dp,site,slot,src,dst,sb,d,hl,sz) target infos (st,so,ho) x s <=>
  abi_site_members_index guard world origin resources
    (active,dp,site,slot,src,dst,sb,d,hl,sz) target infos (st,so,ho) x s /\
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out0,end0) /\
  guard st end0
End

Theorem abi_site_members_scoped_source:
  abi_site_members_scoped guard terminal (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (st,so,ho) x s ==>
  (?sw. eval_operand src s = SOME sw) /\ fresh_vars_wrt limit_st s
Proof
  PairCases_on `terminal` >>
  simp_tac bool_ss [abi_site_members_scoped_def] >> strip_tac >>
  drule abi_site_members_index_source >> simp[]
QED

Theorem abi_site_members_scoped_cons_ledger:
  abi_encoder_hereditary_guard guard /\
  abi_site_members_scoped guard (out0,end0) (ctx,func) (origin,initial)
    resources (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) x s /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp)
    ((ei,az,mz,dyn)::infos) (st,so,ho) (out,en) /\
  abi_encoder_spine_cons_layout func limit_st hi (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) ==>
  out = out0 /\ en = end0 /\ guard p ce /\ guard ce end0 /\
  compile_abi_encode_complex_elems dst src infos (so+mz) (ho+az) dp ce = (out0,end0)
Proof
  simp_tac bool_ss [abi_site_members_scoped_def] >> strip_tac >>
  drule_all abi_encoder_members_cons_guard >> simp[]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Scoped encoder member dependency" else ()
  end) [abi_site_members_scoped_source, abi_site_members_scoped_cons_ledger];

Definition abi_site_members_child_pre_def:
  abi_site_members_child_pre resources guard (dyn,value,cursor) c s <=>
    if dyn then abi_encoder_member_dynamic_pre value resources guard cursor c s
    else abi_encoder_child_ready value resources guard c s
End

Definition abi_site_members_child_post_def:
  abi_site_members_child_post (ctx,func) resources guard (dyn,value,cursor) c s t <=>
    if dyn then abi_encoder_member_dynamic_post (ctx,func) value resources guard cursor c s t
    else abi_encoder_child_post (ctx,func) value resources c s t
End

Theorem abi_site_members_child_dispatch:
  abi_site_members_child_pre resources guard (T,value,cursor) =
    abi_encoder_member_dynamic_pre value resources guard cursor /\
  abi_site_members_child_pre resources guard (F,value,cursor) =
    abi_encoder_child_ready value resources guard /\
  abi_site_members_child_post (ctx,func) resources guard (T,value,cursor) =
    abi_encoder_member_dynamic_post (ctx,func) value resources guard cursor /\
  abi_site_members_child_post (ctx,func) resources guard (F,value,cursor) =
    abi_encoder_child_post (ctx,func) value resources
Proof
  simp[FUN_EQ_THM, abi_site_members_child_pre_def, abi_site_members_child_post_def]
QED

Theorem abi_site_members_child_run:
  !y c r. abi_encoder_spine_core_code func c /\
    abi_site_members_child_pre resources guard y c r ==>
    ?u. abi_decode_sim ctx func r u /\
      abi_site_members_child_post (ctx,func) resources guard y c r u
Proof
  rpt gen_tac >> PairCases_on `y` >> Cases_on `y0` >>
  simp_tac bool_ss [abi_site_members_child_pre_def,
    abi_site_members_child_post_def, pairTheory.UNCURRY_DEF] >>
  rpt strip_tac
  >- (irule abi_encoder_member_dynamic_run >> asm_rewrite_tac []) >>
  irule abi_encoder_child_ready_run >> asm_rewrite_tac [] >>
  qexists_tac `guard` >> asm_rewrite_tac []
QED

Theorem abi_site_members_index_cons_shape:
  abi_site_members_index guard (ctx,func) (origin,initial)
    resources (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) x s ==>
  ?ty tys av avs pre pvs. x = (ty::tys,av::avs,pre,pvs)
Proof
  PairCases_on `resources` >> PairCases_on `target` >> PairCases_on `x` >>
  simp_tac bool_ss [abi_site_members_index_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_site_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_members_inv_def]) >>
  qpat_assum `abi_site_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_members_pre_def]) >>
  `LENGTH ((ei,az,mz,dyn)::infos) = LENGTH x0 /\ LENGTH x0 = LENGTH x1` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _`
       (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp_tac (srw_ss()) [abi_encoder_complex_input_iff, abi_encoder_tuple_type_def] >>
     rpt strip_tac >> gvs[]) >>
  Cases_on `x0` >- gvs[] >> Cases_on `x1` >- gvs[] >> simp[]
QED

Theorem abi_site_members_empty_post:
  abi_encoder_spine_code func limit_st hi (dst,src,dp) [] (st,so,ho) (out,en) /\
  abi_site_members_index guard (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_site_members_inv [] [] [] all_tys all_avs active dp site slot A lo
    en limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_site_encoder_effect A lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_site_members_index_empty >> strip_tac >>
  qpat_assum `abi_encoder_spine_code _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_code_def]) >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[]
QED

Definition abi_site_members_entry_def:
  abi_site_members_entry guard (out0,end0) (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y <=>
  ?ty tys av avs pre pvs.
    x = (ty::tys,av::avs,pre,pvs) /\
    abi_site_members_index guard (ctx,func) (origin,initial)
      (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
      target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
    abi_site_encoder_input ei ty av p elem_src dst (sb+so) mz d sz A b cap r /\
    compile_abi_encode_child dst elem_src ei dyn ho dp p = (len,ce) /\
    fn_has_code p ce func /\
    (p.cs_blocks = ce.cs_blocks \/
      !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    ce.cs_next_id <= hi /\ ce.cs_next_var <= limit_st.cs_next_var /\
    guard p ce /\ guard ce end0 /\
    compile_abi_encode_complex_elems dst src infos (so+mz) (ho+az) dp ce = (out0,end0) /\
    (if dyn then ?ops prepared.
       abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
       y = (T,(ty,av,sb+so,mz,d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))),
         (FST ops,FST (SND ops),dp,d+ho,hl+LENGTH (FLAT (abi_tuple_tails pre pvs)),slot,site))
     else y = (F,(ty,av,sb+so,mz,d+ho),(dst,dst,dp,d+ho,0,slot,site)))
End

Theorem abi_site_members_entry_prepare:
  abi_encoder_hereditary_guard guard /\
  abi_site_members_scoped guard (out0,end0) (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) x s /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp)
    ((ei,az,mz,dyn)::infos) (st,so,ho) (out,en) /\
  abi_encoder_spine_cons_layout func limit_st hi (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  abi_encoder_member_phase_raw st p s r ==>
  ?y. abi_site_members_entry guard (out0,end0) (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y
Proof
  strip_tac >> drule_all abi_site_members_scoped_cons_ledger >> strip_tac >>
  qpat_assum `abi_site_members_scoped _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_members_scoped_def]) >>
  drule abi_site_members_index_cons_shape >> strip_tac >>
  qpat_x_assum `x = _` SUBST_ALL_TAC >>
  drule_all abi_site_members_index_prepare >> strip_tac >>
  qpat_assum `abi_encoder_spine_cons_layout _ _ hi _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_cons_layout_def]) >>
  qpat_assum `abi_encoder_spine_code _ _ hi _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_code_def]) >>
  `ce.cs_next_id <= hi /\ ce.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  simp_tac bool_ss [abi_site_members_entry_def] >>
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

Theorem abi_site_members_entry_input:
  abi_encoder_hereditary_guard guard /\
  abi_site_members_entry guard terminal (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y ==>
  abi_encoder_spine_child_input func limit_st
    (abi_site_members_child_pre (A,b,cap,limit_st) guard y)
    (abi_site_members_child_post (ctx,func) (A,b,cap,limit_st) guard y)
    (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `terminal` >>
  simp_tac bool_ss [abi_site_members_entry_def, PULL_EXISTS] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `dyn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      simp_tac bool_ss [] >> ntac 2 (disch_then (CHOOSE_THEN mp_tac)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `y = _` SUBST1_TAC >>
      simp_tac bool_ss [abi_site_members_child_dispatch] >>
      `!child_len child_end.
        compile_abi_encode_to_buf (SND (SND ops)) elem_src ei prepared =
          (child_len,child_end) ==> guard prepared child_end` by
        (rpt strip_tac >> drule_all abi_encoder_dynamic_child_guard >> simp[]) >>
      drule_all (SRULE [] (Q.INST
        [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
        abi_site_members_dynamic_request)) >> simp[]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp_tac bool_ss [] >>
  disch_then SUBST1_TAC >>
  simp_tac bool_ss [abi_site_members_child_dispatch] >>
  `!head prepared. emit_op ADD [dst;Lit (n2w ho)] p = (head,prepared) ==>
    guard prepared ce` by
    (rpt strip_tac >> drule_all abi_encoder_static_child_guard >> simp[]) >>
  drule_all abi_site_members_static_request >> simp[]
QED

Theorem abi_site_members_entry_exit:
  abi_site_members_entry guard (out0,end0) (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz) target
    (ei,az,mz,dyn,infos) (st,so,ho) x s (elem_src,p,len,ce) r y /\
  abi_encoder_spine_child_output
    (abi_site_members_child_post (ctx,func) (A,b,cap,limit_st) guard y)
    (ei,dyn,dst,elem_src,ho,dp,p,ce,len) r u ==>
  ?x'. abi_site_members_scoped guard (out0,end0) (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) x' u
Proof
  simp_tac bool_ss [abi_site_members_entry_def, PULL_EXISTS] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_site_members_scoped_def] >>
  asm_rewrite_tac [] >>
  Cases_on `dyn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      simp_tac bool_ss [] >> ntac 2 (disch_then (CHOOSE_THEN mp_tac)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `y = _` SUBST_ALL_TAC >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_site_members_child_dispatch]) >>
      drule_all (SRULE [] (Q.INST
        [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
        abi_site_members_dynamic_exit)) >>
      disch_then assume_tac >> goal_assum (drule_at Any)) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp_tac bool_ss [] >>
  disch_then SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_site_members_child_dispatch]) >>
  drule_all abi_site_members_static_exit >>
  disch_then assume_tac >> goal_assum (drule_at Any)
QED

Theorem abi_site_members_scoped_empty_post:
  abi_encoder_spine_code func limit_st hi (dst,src,dp) [] (st,so,ho) (out,en) /\
  abi_site_members_scoped guard terminal (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) [] (st,so,ho) x s ==>
  abi_site_members_inv [] [] [] all_tys all_avs active dp site slot A lo
    en limit_st src dst sb end_so end_ho d hl sz b cap s /\
  abi_site_encoder_effect A lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s
Proof
  PairCases_on `terminal` >>
  simp_tac bool_ss [abi_site_members_scoped_def] >> strip_tac >>
  drule_all abi_site_members_empty_post >> simp[]
QED

Theorem abi_site_members_generate:
  abi_encoder_hereditary_guard guard /\ guard st en /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_site_members_index guard (ctx,func) (origin,initial)
    (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s ==>
  ?t. abi_encoder_member_spine (\c r u. abi_decode_sim ctx func r u)
      (dst,src,dp) infos (st,so,ho) (out,en) s t /\
    abi_site_members_inv [] [] [] all_tys all_avs active dp site slot A lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_site_encoder_effect A lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  strip_tac >>
  mp_tac (SRULE [] (Q.SPECL [
    `abi_site_members_child_pre (A,b,cap,limit_st) guard`,
    `abi_site_members_child_post (ctx,func) (A,b,cap,limit_st) guard`,
    `\c r u. abi_decode_sim ctx func r u`,
    `\(out,en) t.
      abi_site_members_inv [] [] [] all_tys all_avs active dp site slot A lo
        en limit_st src dst sb end_so end_ho d hl sz b cap t /\
      abi_site_encoder_effect A lo hi origin.cs_next_var limit_st d sz b cap initial t /\
      abi_decode_sim ctx func initial t`, `hi`] (Q.ISPECL [
    `abi_site_members_scoped guard (out,en) (ctx,func) (origin,initial)
      (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
      (all_tys,all_avs,end_so,end_ho)`,
    `\i (st:compile_state,so,ho) x (s:venom_state).
      abi_site_members_entry guard (out,en) (ctx,func) (origin,initial)
        (A,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
        (all_tys,all_avs,end_so,end_ho) i (st,so,ho) x s`]
    (Q.GENL [`Inv`,`Entry`,`child_pre`,`child_post`,`core_run`,`Post`,`last`]
      abi_encoder_member_spine_generate)))) >>
  simp_tac bool_ss [] >> impl_tac
  >- (conj_tac >- MATCH_ACCEPT_TAC abi_site_members_child_run >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_site_members_scoped_source) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_all abi_site_members_entry_prepare >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> drule_all abi_site_members_entry_input >> simp[]) >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_site_members_entry_exit) >>
      rpt gen_tac >> MATCH_ACCEPT_TAC abi_site_members_scoped_empty_post) >>
  disch_then (qspecl_then [`infos`,`st`,`so`,`ho`,`out`,`en`,`x`,`s`] mp_tac) >>
  asm_rewrite_tac [] >>
  impl_tac >- (simp[abi_site_members_scoped_def] >>
    fs[abi_encoder_spine_code_def]) >> simp[]
QED

Theorem abi_scratch_members_index_interval:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (st,so,ho) x s /\ st.cs_next_id <= last /\ hi <= last ==>
  abi_site_members_index (\st en. first <= st.cs_next_id /\ en.cs_next_id <= last)
    (ctx,func) (origin,initial)
    (abi_decoder_ids first last,lo,hi,b,cap,limit_st)
    (active,dp,site,slot,src,dst,sb,d,hl,sz) target infos (st,so,ho) x s
Proof
  PairCases_on `target` >> PairCases_on `x` >> strip_tac >>
  `first <= lo` by fs[abi_scratch_members_index_def, abi_scratch_members_inv_def] >>
  fs[abi_scratch_members_index_def] >>
  asm_simp_tac bool_ss [abi_site_members_index_def, abi_site_members_inv_interval,
    abi_site_encoder_effect_interval] >>
  irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
  metis_tac[abi_encoder_child_capability_interval]
QED

Theorem abi_scratch_members_generate:
  hi <= last /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s ==>
  ?t. abi_encoder_member_spine (\c r u. abi_decode_sim ctx func r u)
      (dst,src,dp) infos (st,so,ho) (out,en) s t /\
    abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  strip_tac >> PairCases_on `x` >>
  `st.cs_next_id <= en.cs_next_id` by
    (qpat_assum `abi_encoder_spine_code _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_spine_code_def] >> strip_tac >>
     mp_tac (Q.SPECL [`dst`,`src`,`infos`,`so`,`ho`,`dp`,`st`]
       (REWRITE_RULE [abi_encoder_counters_mono_def] (cj 3 abi_encoder_counters_mono_mutual))) >>
     asm_rewrite_tac [] >> simp[]) >>
  `st.cs_next_id <= last /\ en.cs_next_id <= last /\ first <= st.cs_next_id /\ first <= lo` by
    (fs[abi_encoder_spine_code_def, abi_scratch_members_index_def,
      abi_scratch_members_inv_def] >> decide_tac) >>
  drule_all abi_scratch_members_index_interval >> strip_tac >>
  drule_all (SRULE [abi_encoder_hereditary_guard_interval] (Q.INST
    [`guard` |-> `\st en. first <= st.cs_next_id /\ en.cs_next_id <= last`]
    abi_site_members_generate)) >> strip_tac >>
  qexists_tac `t` >>
  asm_rewrite_tac [] >>
  metis_tac[abi_site_members_inv_interval, abi_site_encoder_effect_interval]
QED

(* Both clients must remain kernel-closed, independently of unrelated admissions. *)
val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if not (null (Thm.hyp th)) orelse not (null axs) orelse
       List.exists (fn s => s <> "DISK_THM") ors
    then raise Fail "Encoder member interpretation dependency" else ()
  end) [abi_site_members_scoped_source, abi_site_members_scoped_cons_ledger,
    abi_site_members_child_dispatch, abi_site_members_child_run,
    abi_site_members_index_cons_shape, abi_site_members_empty_post,
    abi_site_members_entry_prepare, abi_site_members_entry_input,
    abi_site_members_entry_exit, abi_site_members_scoped_empty_post,
    abi_site_members_generate, abi_scratch_members_index_interval,
    abi_scratch_members_generate];
