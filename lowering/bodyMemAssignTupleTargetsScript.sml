(* Memory case of the body induction, assignment to a tuple of local, scalar
   toplevel and storage word-field targets (bodyMemAssignTuple's dispatch):
   the memory twin of S1's body_assign_tuple_targets (bodySimStmtCases). *)
Theory bodyMemAssignTupleTargets
Ancestors
  bodyMemoryPreds bodyMemAssignTupleTargetsFacts bodyMemAssignTupleTargetsWrapper
  bodySimStmtCases bodyMemAssignTupleLocalsPrep
  tupleTargetStoreProps bodyExprPreFacts bodySim bodyMemoryDefs exprSimDefs
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants exprSimHypsDefs
  supportedStmts supportedExprs stmtSimDefs loweringPosts
  list rich_list exprLoweringProps compileEnv loweringStateRelDefs vyperTypeValues
  vyperTyping vyperTypeDefaults vyperTypeExprSoundness exprSimSource
  compileVyper vyperCompiler vyperTypeExprResult
Libs
  monadsyntax

Theorem body_assign_tuple_targets_mem:
  !cx gs e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_stmt_safe tops (Assign (TupleTarget gs) e) /\
    body_expr_mem_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt strip_tac >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (simp[stmt_frag_mem_def] >> rpt strip_tac >>
      fs[stmt_state_rel_def, state_rel_def]) >>
  drule tuple_targets_typing >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (irule body_assign_tuple_rhs_pre >> metis_tac[]) >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH] >>
  `!i. i < LENGTH gs ==>
     tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
     (~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
     !es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type (EL i tvs) v ==>
       tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) v` by
    (qx_gen_tac `i` >> disch_tac >> irule body_tuple_target_ready >>
     fs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `gs <> []` by (strip_tac >> gvs[assignable_type_def]) >>
  irule compile_assign_tuple_targets_stmt_frag_mem >>
  simp[] >> rpt conj_tac
  >~ [`expr_sim_mem _ _ _ _ _ _ _`] >- metis_tac[body_expr_mem_ok_def]
  >~ [`cenv.ce_target CapMcopy`]
  >- (qpat_x_assum `body_inv _ _ _ _` mp_tac >>
      rw[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
      >- (gvs[lower_vyper_deploy_unit_def, AllCaseEqs()] >>
          rpt (pairarg_tac >> gvs[]) >>
          gvs[run_deploy_lowering_def, AllCaseEqs(), lowering_policy_ok_def]) >>
      gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[run_lowering_def, AllCaseEqs(), lowering_policy_ok_def])
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound >> metis_tac[])
  >~ [`tuple_target_layout _ _ _ _ _`]
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
      drule_all expr_body_pre_eval >> strip_tac >>
      gvs[expr_result_typed_def, value_result_typed_def, expr_runtime_typed_def,
          value_runtime_typed_def, value_has_type_def,
          values_have_types_LIST_REL, LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
      drule_all expr_body_pre_eval >> strip_tac >>
      gvs[expr_result_typed_def, value_result_typed_def, expr_runtime_typed_def,
          value_runtime_typed_def])
  >> metis_tac[]
QED
