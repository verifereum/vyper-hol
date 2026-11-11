(* Body metadata discharge for counted memory Append. *)
Theory bodyMemAppendAdapter
Ancestors
  bodyMemAppendCompose bodyAppendStorageAdapter bodyMemoryPreds
  bodyAppendStorageFacts bodyExprPreFacts stmtSimDefs exprSimMemDefs
  exprSimSource exprSimHypsDefs stmtSimAssignStorage bodySim exprSimHyps
  supportedStmts supportedStmtTraverse vyperStorageLayoutSafety
  vyperTypeSystem vyperTypeValues compileEnv loweringStateRelDefs vyperTypeCallGraph vyperState
  vyperInterpreter vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeExprResult supportedDecls supportedTypes vyperValue bodyStorageMetadata
  exprLoweringProps
Libs
  monadsyntax

Theorem stmt_frag_mem_storage_rel_discharge[local]:
  ((storage_vars_rel cenv cx /\ transient_vars_rel cenv cx) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv m source es) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv m source es
Proof
  strip_tac >> rewrite_tac[stmt_frag_mem_def] >>
  rpt gen_tac >> strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `_ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_mem_def]) >>
  simp[] >> metis_tac[]
QED

Theorem body_append_storage_fragment_mem:
  body_stmt_safe tops (Append (TopLevelNameTarget (src,id)) e) /\
  (!s p t. eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,t) ==>
             body_expr_mem_ok cx e) /\
  body_inv tops ctx cenv cx /\ supported_storage_dynamic_array tops (src,id) /\
  supported_expr tops e /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget (src,id)) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
              (Append (TopLevelNameTarget (src,id)) e) ==>
            occurs_abi_decode_target target tops) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
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
  `body_expr_mem_ok cx e` by metis_tac[] >>
  `expr_sim_mem ctx func cenv cx elem e es` by metis_tac[body_expr_mem_ok_def] >>
  `get_module_code cx src = SOME tops` by
    (drule supported_append_storage_decl >> strip_tac >>
     drule supported_variable_decl_mem >> strip_tac >> gvs[body_inv_def]) >>
  irule stmt_frag_mem_storage_rel_discharge >> strip_tac >>
  drule_all append_storage_compiler_location >> strip_tac >>
  `type_memory_bytes cenv elem = 32` by
    (gvs[supported_full_word_type_def] >> simp[type_memory_bytes_def]) >>
  gvs[evaluate_type_def] >>
  irule compile_append_storage_word_stmt_frag_mem >> simp[] >>
  qexistsl_tac [`src`, `id`] >>
  simp[declared_storage_region_def, evaluate_type_def] >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule body_append_word_encoding >> simp[] >>
  disch_then irule >> simp[] >> metis_tac[]
QED
