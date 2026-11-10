Theory bodyIfExpArmOutcome
Ancestors
  context loweringPosts exprLowering exprSimMemDefs
  gasOutcome gasSummary fragGasMode fragGasPath
  bodyIfExpSelectedMemory bodyIfExpBytesAdapter exprSimMemUnwrap
  exprSimUnwrapProps exprSimUnwrap exprLoweringProps fragGasPathMem

Theorem ifexp_selected_arm_path_mem:
  post_value_type ce e = expr_type e /\
  expr_type e = t /\ at = lowered_value_type ce e /\ ~is_word_type t /\
  (~same_memory_layout ce at t ==> is_bytestring_type t) /\
  compile_ifexp_arm ce t at vv sm = (op,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
     type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64) /\
  (!tv. same_memory_layout ce at t /\ evaluate_type (get_tenv cx) t = SOME tv ==>
     ?avt. evaluate_type (get_tenv cx) at = SOME avt /\
       type_memory_size tv <= type_memory_size avt) /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  vv_store_bound cx t at ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> Cases_on `same_memory_layout ce at t`
  >- suspend "same" >>
  irule ifexp_bytestring_adapter_path_mem >> simp[] >>
  conj_tac >- (qpat_x_assum `!tv. _ ==> _ /\ _` drule >> simp[]) >>
  qexistsl_tac [`at`,`sm`,`vv`] >> gvs[]
QED

Resume ifexp_selected_arm_path_mem[same]:
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  Cases_on `vv` >- suspend "stack" >>
  rename1 `LocatedValue vt p` >>
  Cases_on `p.ptr_location = LocMemory` >- suspend "memory" >>
  `vt = t` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value v) _ _` mp_tac >>
     qpat_assum `post_value_type ce e = _`
       (fn th => rewrite_tac[vv_post_def, vv_holds_def, th]) >>
     qpat_assum `expr_type e = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `~(p.ptr_location = LocMemory)` (fn th => rewrite_tac[th]) >>
     strip_tac >> simp[]) >>
  qpat_x_assum `vt = t` SUBST_ALL_TAC >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   p.ptr_location = LocCode` by
    (Cases_on `p.ptr_location` >> fs[] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCalldata` (fn th =>
       simp_tac (srw_ss()) [vv_post_def, vv_holds_def, th])) >>
  (`unwrap_value ce (LocatedValue t p) sm = (op,sb)` by
    fs[compile_ifexp_arm_def] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_copy_capacity_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[vv_operand_def] >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  fs[vv_store_bound_def, vyperStateTheory.read_result_def,
     vyperStateTheory.return_def] >> metis_tac[])
QED

Resume ifexp_selected_arm_path_mem[stack]:
  fs[compile_ifexp_arm_def, unwrap_value_def, compileEnvTheory.comp_return_def] >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- metis_tac[gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
  drule_all ifexp_arm_store_bound >>
  simp[vv_store_bound_def, contextTheory.mk_ptr_def]
QED

Resume ifexp_selected_arm_path_mem[memory]:
  `~is_word_type vt` by
    (`vt = t \/ is_bytestring_type vt` suffices_by
       metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value v) _ _` mp_tac >>
     qpat_assum `post_value_type ce e = _`
       (fn th => rewrite_tac[vv_post_def, vv_holds_def, th]) >>
     qpat_assum `expr_type e = _` (fn th => rewrite_tac[th]) >>
     strip_tac >> simp[]) >>
  `vv_store_bound cx t t ee raw (LocatedValue vt p) s` by
    (irule ifexp_arm_store_bound >> metis_tac[]) >>
  gvs[compile_ifexp_arm_def, unwrap_value_def, compileEnvTheory.comp_return_def] >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- metis_tac[gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  fs[vv_store_bound_def, mk_ptr_def]
QED

Finalise ifexp_selected_arm_path_mem

Theorem ifexp_outcome_suffix_mem:
  gas_outcome T tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u /\ ~u.vs_halted ==>
     ?v. gas_path_mem ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome T tops (ctx,func) source (es,s0) Q' R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks` >>
  Cases_on `gas_summary_at T (ctx,func) marks source (es,s0) Q R`
  >- (disj1_tac >>
      fs[gas_summary_at_def] >>
      Cases_on `?u. r = OK u /\ Q res (es_end with gas_obs := []) u`
      >- (gvs[] >>
          `~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             drule gas_path_mem_exec >> metis_tac[gas_path_normal]) >>
          first_x_assum drule_all >> strip_tac >>
          qexistsl_tac [`res`,`es_end`,`OK v`] >> simp[] >>
          gvs[gas_marked_exec_def, gas_marked_path_def] >>
          metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
      metis_tac[]) >> metis_tac[]
QED

Theorem ifexp_selected_arm_outcome_mem:
  post_value_type ce e = expr_type e /\
  expr_type e = t /\ ~is_word_type t /\
  (~same_memory_layout ce (lowered_value_type ce e) t ==> is_bytestring_type t) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
    type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64) /\
  (!tv. same_memory_layout ce (lowered_value_type ce e) t /\
    evaluate_type (get_tenv cx) t = SOME tv ==>
    ?avt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME avt /\
      type_memory_size tv <= type_memory_size avt) /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  gas_outcome T tops (ctx,func) source (es,s0)
    (\res ee s. ?raw v tvt. res = INL raw /\
      read_result cx raw ee = (INL v,ee) /\
      evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
      vv_store_bound cx t (lowered_value_type ce e) ee raw vv s /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) R ==>
  gas_outcome T tops (ctx,func) source (es,s0)
    (\res ee s. ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
      expr_post ctx func ce cx e es sa sb s0 ee v op s /\
      vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) s /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) R
Proof
  strip_tac >> irule ifexp_outcome_suffix_mem >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  drule ifexp_selected_arm_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `u'` >> simp[] >> metis_tac[]
QED
