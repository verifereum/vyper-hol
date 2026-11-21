(* Body-side discharge for primitive storage Append. *)
Theory bodyAppendStorageAdapter
Ancestors
  supportedExprTraverse supportedExprs loweringPosts exprLowering vyperAST allocLimits allocLimitsProps
  vyperTyping valueEncodingTyping exprSimProps
  stmtSimDefs exprSimSource exprSimHypsDefs
  bodyAppendStorageFacts bodyAppendStorageLayoutFacts bodyExprPreFacts stmtSimAppendStorageCompose
  stmtSimAssignStorageFacts bodySim supportedStmts supportedStmtTraverse
  vyperStorageLayoutSafety vyperTypeSystem vyperTypeValues compileEnv loweringStateRelDefs
  vyperTypeCallGraph vyperState vyperInterpreter
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  supportedDecls supportedTypes vyperValue bodyStorageMetadata
  gasOutcome gasStorage gasSummary vyperStorageTrace vyperStorageFootprint
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
  strip_tac >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  drule supported_expr_body_calls >> strip_tac >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
  `~is_extcode e` by
    (irule alloc_limits_expr_not_extcode >> qexists_tac `cenv` >>
     fs[stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
  `cx_tops cx = tops` by metis_tac[gasContextTheory.cx_tops_module] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem append_aggregate_lowered_type:
  !cenv e env. ~is_bytestring_type (expr_type e) /\ int_calls_expr e = [] /\
    well_typed_expr env e ==> lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  rw[lowered_value_type_def, expr_type_def, int_calls_expr_def,
     is_bytestring_type_def] >>
  gvs[well_typed_expr_def, well_typed_builtin_app_def,
      type_builtin_result_ok_def, well_typed_type_builtin_args_def, AllCaseEqs(),
      is_bytestring_type_def, concat_buffer_type_def]
QED

