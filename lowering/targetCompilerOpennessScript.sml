(* Compiler openness for successfully evaluated place targets. *)
Theory targetCompilerOpenness
Ancestors
  targetStorageContinuationMemory targetSubscriptSplit targetPlaceSimCasesBase
  bodySimStmtCases exprOpenTerminals exprOpenPrimitives exprLowering
  compileEnv vyperInterpreter vyperState targetPlaceSim exprSimHypsDefs
  targetPlaceLive targetSubscriptContinuation
Libs
  pairLib

Theorem target_compiler_open:
  !bt tops ctx cenv cx env es pv ee sa rb sm.
    body_inv tops ctx cenv cx /\
    EVERY (supported_expr tops) (target_indices bt) /\
    target_pre cenv cx env bt es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_base_place cx bt es = (INL pv,ee) /\
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    ~block_is_terminated sa ==> ~block_is_terminated sm
Proof
  recInduct base_assignment_target_induct >> rpt strip_tac
  >- (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[compile_get_target_ptr_def, comp_return_def] >>
      Cases_on `x` >> gvs[comp_return_def])
  >- (Cases_on `FLOOKUP cenv.ce_module_vars nsid` >>
      gvs[compile_get_target_ptr_def, comp_return_def] >>
      Cases_on `x` >> gvs[comp_return_def])
  >- suspend "subscript" >>
  suspend "attribute"
QED

Resume target_compiler_open[subscript]:
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, bind_def, AllCaseEqs()]) >>
  gvs[target_indices_def] >>
  drule target_subscript_compile_decompose >> strip_tac >> gvs[] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `~block_is_terminated sm'` by metis_tac[] >>
  `expr_sim_inv cenv cx env s''` by metis_tac[eval_base_place_sim_inv] >>
  `expr_body_pre cenv cx env e s''` by fs[target_pre_def, target_indices_pre_def] >>
  `~block_is_terminated sn` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
     irule unwrap_value_open >> goal_assum (drule_at Any) >>
     irule compile_expr_open >> goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `SND (SND rb')`
  >- (qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
      simp[target_subscript_suffix_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >> metis_tac[compile_array_subscript_open]) >>
  Cases_on `x` >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  simp[target_subscript_suffix_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >> metis_tac[compile_mapping_subscript_open]) >>
  metis_tac[compile_array_subscript_open]
QED

Resume target_compiler_open[attribute]:
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, bind_def, AllCaseEqs()]) >>
  gvs[target_indices_def] >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `target_pre cenv cx env bt es` by fs[target_pre_def, target_indices_pre_def, immutable_root_def, target_root_def] >>
  `~block_is_terminated sm'` by metis_tac[] >>
  drule emit_op_nonterminator_open >> simp[venomInstTheory.is_terminator_def]
QED

Finalise target_compiler_open
