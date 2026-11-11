(* Body-side discharge for primitive storage Append. *)
Theory bodyAppendStorageAdapter
Ancestors
  supportedExprTraverse allocLimits allocLimitsProps
  stmtSimDefs exprSimSource exprSimHypsDefs
  bodyAppendStorageFacts bodyExprPreFacts stmtSimAppendStorageCompose
  stmtSimAssignStorage bodySim exprSimHyps supportedStmts supportedStmtTraverse
  vyperStorageLayoutSafety vyperTypeSystem vyperTypeValues compileEnv loweringStateRelDefs
  vyperTypeCallGraph vyperState vyperInterpreter
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  supportedDecls supportedTypes vyperValue bodyStorageMetadata
Libs
  monadsyntax

Theorem body_append_expr_pre:
  body_stmt_safe tops (Append (TopLevelNameTarget nid) e) /\
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (Append (TopLevelNameTarget nid) e) ==>
            occurs_abi_decode_target target tops) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >> qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>

  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    fs[body_inv_def] >>
  `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      int_calls_stmt_def, int_calls_expr_def, body_inv_def] >>
  rpt conj_tac
  >~ [`call_evaluation_safe`] >- (qexists_tac `[]` >> simp[]) >>
  metis_tac[]
QED

Theorem body_append_word_encoding:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) ==>
  encode_value tv v = SOME [(0,typed_val_to_w256 tv v)]
Proof
  strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  metis_tac[encode_value_word_typed]
QED

Theorem stmt_frag_storage_rel_discharge[local]:
  ((storage_vars_rel cenv cx /\ transient_vars_rel cenv cx) ==>
    stmt_frag ctx func cx lctx RetQ cenv m source es) ==>
  stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  strip_tac >>
  rewrite_tac[stmtSimDefsTheory.stmt_frag_def,
              stmtSimDefsTheory.stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `_ ==> stmt_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmtSimDefsTheory.stmt_frag_def,
                            stmtSimDefsTheory.stmt_framed_frag_def]) >>
  simp[] >> metis_tac[]
QED

Theorem body_append_storage_fragment:
  body_stmt_safe tops (Append (TopLevelNameTarget (src,id)) e) /\
  (!s p t. eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,t) ==>
             body_expr_ok cx e) /\
  body_inv tops ctx cenv cx /\ supported_storage_dynamic_array tops (src,id) /\
  supported_expr tops e /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget (src,id)) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (Append (TopLevelNameTarget (src,id)) e) ==>
            occurs_abi_decode_target target tops) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget (src,id)) e))
    (eval_stmt cx (Append (TopLevelNameTarget (src,id)) e)) es
Proof
  strip_tac >> drule_all body_append_target_bounds >> strip_tac >>
  drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all body_append_runtime_metadata >> strip_tac >> gvs[] >>
  drule supported_append_element_layout >>
  disch_then (qspec_then `get_tenv cx` strip_assume_tac) >>
  `expr_type e = elem` by metis_tac[type_widens_to_word] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_append_expr_pre] >>
  `body_expr_ok cx e` by metis_tac[] >>
  `expr_sim ctx func cenv cx elem e es` by metis_tac[body_expr_ok_def] >>
  `get_module_code cx src = SOME tops` by
    (drule supported_append_storage_decl >> strip_tac >>
     drule supported_variable_decl_mem >> strip_tac >> gvs[body_inv_def]) >>
  irule stmt_frag_storage_rel_discharge >> strip_tac >>
  drule_all append_storage_compiler_location >> strip_tac >>
  `type_memory_bytes cenv elem = 32` by
    (gvs[supported_full_word_type_def] >> simp[type_memory_bytes_def]) >>
  gvs[evaluate_type_def] >>
  irule compile_append_storage_word_stmt_frag >>
  simp[] >>
  qexistsl_tac [`src`, `id`] >>
  simp[declared_storage_region_def, evaluate_type_def] >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule body_append_word_encoding >> simp[] >>
  disch_then irule >> simp[] >> metis_tac[]
QED
