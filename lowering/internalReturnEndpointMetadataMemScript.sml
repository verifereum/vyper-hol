Theory internalReturnEndpointMetadataMem
Ancestors
  exprSimHypsDefs vyperEvalPreservesScopes vyperTypeEnvPreservation
  bodySim compileEnv vyperState vyperTypeInvariants

Theorem return_read_preserves_tv[local]:
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  preserves_tv cx es ee
Proof
  simp[vyperStateTheory.bind_def] >>
  Cases_on `eval_expr cx e es` >> Cases_on `q` >> simp[] >>
  strip_tac >> drule read_result_state >> strip_tac >> gvs[] >>
  drule eval_expr_preserves_tv >> simp[]
QED

Theorem internal_return_endpoint_constructor_separation:
  same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
  (cenv.ce_is_ctor ==> !nm off ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) cap) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) = (INL v,ee)
  ==>
  (cenv'.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv'.ce_module_vars (cenv'.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv'.ce_module imms) name = SOME (itv,iv)
    ==> regions_disjoint off (type_memory_size itv) (w2n bw) cap)
Proof
  strip_tac >> drule return_read_preserves_tv >> strip_tac >>
  gvs[same_frame_def, compile_env_component_equality] >>
  fs[expr_sim_inv_def, bare_globals_layout_def,
     env_consistent_def, env_immutables_consistent_def] >>
  rpt strip_tac >>
  `?ity. FLOOKUP env.bare_globals (cenv.ce_module,name) = SOME ity`
    by metis_tac[] >>
  `IS_SOME (FLOOKUP (get_source_immutables cenv.ce_module
      (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m)) name)`
    by metis_tac[] >>
  Cases_on `FLOOKUP (get_source_immutables cenv.ce_module
      (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m)) name` >>
  gvs[] >> PairCases_on `x` >>
  `evaluate_type (get_tenv cx) ity = SOME x0` by metis_tac[] >>
  `?iv'. FLOOKUP (get_source_immutables cenv.ce_module
      (case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m)) name =
      SOME (x0,iv')`
    by (irule preserves_tv_immutables_type_preserved >>
        qexistsl [`es with gas_obs := g`, `x1`] >> simp[]) >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >> metis_tac[]
QED
