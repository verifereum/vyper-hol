(* Declaration-level immutable assignment metadata. *)
Theory immutableAssignMetadata
Ancestors
  immutableDeployAssignFacts bodySim bodyStorageMetadata supportedDecls exprSimHypsDefs
  vyperTypeInvariants vyperTypeEnv vyperTypeSystem finite_map exprSimSource
  vyperInterpreter vyperState

Theorem immutable_assign_bare_global:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  expr_sim_inv ce cx env es /\
  supported_immutable_type tops (src,id) = SOME ity ==>
  src = NONE /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (src,id) = SOME ity
Proof
  strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx /\ ce.ce_is_ctor` by
    fs[bodySimTheory.body_inv_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  simp[] >> metis_tac[bare_globals_complete_def]
QED

Theorem immutable_assign_rhs_target:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL r,ee) ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) ee =
    (INL (ImmutablePlace src id []),ee)
Proof
  strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  `env_consistent env cx ee` by fs[expr_sim_inv_def] >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  drule_all env_consistent_bare_global_ready_src >> strip_tac >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  Cases_on `FLOOKUP (get_source_immutables NONE x) id` >>
  gvs[get_source_immutables_def] >>
  rename1 `_ = SOME entry` >> PairCases_on `entry` >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, get_immutables_def,
       get_address_immutables_def, get_place_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def, get_source_immutables_def]
QED
