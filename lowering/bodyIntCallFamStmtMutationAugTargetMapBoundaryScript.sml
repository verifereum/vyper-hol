(* Semantic mapping suffix boundary, independent of the target AST. *)
Theory bodyIntCallFamStmtMutationAugTargetMapBoundary
Ancestors
  bodyIntCallFamStmtMutationAugTargetMapCounted targetSubscriptContinuation
  bodyIntCallJointContract compileEnv exprLoweringProps loweringPosts
  stmtSimAugAssignPlaceMemory loweringShapeRules venomState pair freshWrites
  fragExec exprLowering

Theorem intcall_target_mapping_post_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es0 sa s0 /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sm s0 mid
    (HashMapRef tr slot kt vt) (HashMapT kt vt) rb t /\
  intcall_expr_cont fp ce env mid sm t es sn s /\
  intcall_expr_cont fp ce env es0 sa s0 es sn s /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e mid sm sn t es key ix s /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv fp.jc_cx) kt = SOME tv /\ value_has_type tv key /\
  target_subscript_suffix ce e rb ix sn = (op,sb) /\
  fn_has_code sn sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!l. FST rb <> Label l) /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place fp.jc_cx (HashMapRef tr slot kt vt) (ValueSubscript key) es =
    (INL pv,es') ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 es' pv vt op u /\
      intcall_expr_cont fp ce env es0 sa s0 es' sb u
Proof
  strip_tac >> gvs[] >>
  `eval_operand (FST rb) t = SOME slot /\
   (!x. FST rb = Var x ==> not_fresh_at sm x) /\
   FST (SND rb) = SOME (slot_loc tr) /\
   SND (SND rb) = SOME (MapPT (expr_type e) vt)` by
    (fs[target_post_def, place_ptr_rel_def, value_type_place_def] >> metis_tac[]) >>
  `eval_operand (FST rb) s = SOME slot` by
    (Cases_on `FST rb` >> gvs[eval_operand_def, intcall_expr_cont_def] >>
     metis_tac[]) >>
  `!x. FST rb = Var x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  PairCases_on `rb` >> gvs[] >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  simp[target_subscript_suffix_mapping] >> strip_tac >> gvs[] >>
  `!x. rb0 = Var x \/ ix = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  Cases_on `is_bytestring_type (expr_type e)` >> gvs[]
  >- (`ci_mono sn sh /\ ci_mono sh sb` by
        metis_tac[ci_mono_compile_keccak256_key,
                  ci_mono_compile_mapping_subscript, SND] >>
      `fn_has_code sn sh fp.jc_func /\ fn_has_code sh sb fp.jc_func` by
        (irule fn_has_code_split >> fs[ci_mono_def]) >>
      drule_at (Pat `compile_mapping_subscript _ _ _ = _`)
        intcall_target_mapping_dynamic_suffix >>
      disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  gvs[comp_return_def] >>
  drule_all target_subscript_scalar_key_view >> strip_tac >>
  drule_at (Pat `compile_mapping_subscript _ _ _ = _`)
    intcall_target_mapping_suffix >> disch_then drule_all >> simp[]
QED
