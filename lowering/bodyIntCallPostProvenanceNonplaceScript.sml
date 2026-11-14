(* Structural join of raw effect-free expression ownership certificates. *)
Theory bodyIntCallPostProvenanceNonplace
Ancestors
  bodyIntCallPostProvenanceOrdinary bodyIntCallPostProvenanceTypedCases
  bodyIntCallPostProvenanceLiveSource bodyIntCallPostProvenanceLivePost
  bodyIntCallPostProvenanceStruct bodyIntCallPostProvenanceMakeArray
  bodyIntCallPostProvenanceEmpty bodyIntCallPostProvenanceDecode
  bodyIntCallPostProvenanceConditionalJoin bodyIntCallPostProvenanceSelectorCases
  bodyIntCallPostProvenanceCapturedOutcome bodyIntCallPostProvenanceCaptureAlignment
  exprSimSource exprSimHyps exprLoweringProps exprLowering bodySim
  bodyIntCallArgType bodyIntCallProducerInterface loweringPosts compileEnv
  exprSimDefs exprSimHypsDefs gasOutcome gasSummary vyperAST vyperState context

Theorem intcall_type_builtin_expected_type[local]:
  (tb = Empty \/ ?b. tb = AbiDecode b) ==>
  compile_expr ce expected (TypeBuiltin ann tb target args) sa =
  compile_expr ce ann (TypeBuiltin ann tb target args) sa
Proof
  strip_tac >> gvs[] >>
  simp[compile_expr_type_builtin_dispatch,
       compile_type_builtin_dispatch_component_eq,
       compile_type_builtin_dispatch_body_def]
QED

Theorem intcall_dynarray_free_post[local]:
  vv_post ctx func ce cx e es sa sb s0 ee raw vv t /\
  ~expr_has_effect e /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==> dynarray_free tv) ==>
  intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[effect_free_post_value_type] >>
  gvs[vv_post_def, intcall_vv_provenance_def] >>
  Cases_on `vv` >> gvs[vv_at_def, expr_val_at_def, vv_holds_def, immutable_holds_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_ordinary_outcome[local]:
  expr_vv_case F ctx func ce cx e /\
  expr_body_pre ce cx env e es /\
  (!gs raw ee t. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
    vv_post ctx func ce cx e es sa sb s0 ee raw vv t ==>
    intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t) /\
  compile_expr ce ty e sa = (vv,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?raw. res = INL raw /\
      vv_post ctx func ce cx e es sa sb s0 ee raw vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim ctx func ce cx ty e es` by metis_tac[expr_vv_case_def] >>
  drule (iffLR expr_vv_sim_def) >> disch_then drule_all >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
  gvs[] >>
  `intcall_vv_provenance ce cx (expr_type e) sa sb (es_end with gas_obs := []) tv vv t` by
    (qpat_x_assum `!gs raw ee t. _` irule >> simp[] >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     gvs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED
