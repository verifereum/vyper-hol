(* Declaration-level immutable assignment metadata. *)
Theory immutableAssignMetadata
Ancestors
  immutableDeployAssignFacts bodySim bodyStorageMetadata supportedDecls exprSimHypsDefs
  vyperTypeInvariants vyperTypeEnv vyperTypeSystem finite_map exprSimSource
  vyperInterpreter vyperState bodyInvSplit bodyInvCodeProps
  bodyInvMetadataProps immutableRegionTypingProps alist

Theorem immutable_assign_bare_global_mods:
  contract_inv mods exps ctx ce cx /\ cx.in_deploy /\
  expr_sim_inv_mods mods ce cx env es /\
  ALOOKUP mods src = SOME tops /\
  supported_immutable_type tops (NONE,id) = SOME ity ==>
  ce.ce_is_ctor /\ FLOOKUP env.bare_globals (src,id) = SOME ity
Proof
  strip_tac >>
  `ce.ce_is_ctor` by (drule_then assume_tac contract_inv_constructor >> simp[]) >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (NONE,id)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  drule_all immutable_decl_bare_global_mods >> simp[]
QED

Theorem immutable_assign_bare_global:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  expr_sim_inv ce cx env es /\
  supported_immutable_type tops (src,id) = SOME ity ==>
  src = NONE /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (src,id) = SOME ity
Proof
  Cases_on `src`
  >- (strip_tac >> drule_then assume_tac body_inv_contract >>
      drule_then strip_assume_tac body_inv_main_code >>
      fs[expr_sim_inv_split_def] >>
      irule immutable_assign_bare_global_mods >>
      qexistsl_tac [`ctx`, `cx`, `es`, `[]`, `[(NONE,tops)]`, `tops`] >>
      simp[ALOOKUP_def] >> metis_tac[]) >>
  simp[supported_immutable_type_def, supported_lookup_other_module]
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

(* A deploy-time immutable target names its place without touching the state. *)
Theorem immutable_target_place_state:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_sim_inv ce cx env st ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) st =
    (INL (ImmutablePlace src id []),st)
Proof
  strip_tac >>
  drule_all immutable_assign_bare_global >> strip_tac >>
  `env_consistent env cx st` by fs[expr_sim_inv_def] >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  drule_all env_consistent_bare_global_ready_src >> strip_tac >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  Cases_on `FLOOKUP (get_source_immutables NONE x) id` >>
  gvs[get_source_immutables_def] >>
  rename1 `_ = SOME entry` >> PairCases_on `entry` >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, get_immutables_def,
       get_address_immutables_def, get_place_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def, get_source_immutables_def]
QED
