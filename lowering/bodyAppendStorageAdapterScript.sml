(* Body-side discharge for primitive storage Append. *)
Theory bodyAppendStorageAdapter
Ancestors
  stmtExprAllocationPreProps bodyInvCodeProps compileUnit alist
  supportedExprTraverse supportedExprs loweringPosts exprLowering vyperAST allocLimits allocLimitsProps
  vyperTyping valueEncodingTyping exprSimProps
  stmtSimDefs exprSimSource exprSimHypsDefs
  bodyAppendStorageFacts bodyAppendStorageLayoutFacts bodyExprPreFacts stmtSimAppendStorageCompose
  stmtSimAssignStorageFacts bodySim supportedStmts supportedStmtTraverse
  vyperStorageLayoutSafety vyperTypeSystem vyperTypeValues compileEnv loweringStateRelDefs
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperState vyperInterpreter
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  supportedDecls supportedTypes vyperValue bodyStorageMetadata
  gasOutcome gasStorage gasSummary vyperStorageTrace vyperStorageFootprint
Libs
  monadsyntax

Theorem body_append_expr_pre_mods:
  contract_inv mods exps ctx cenv cx /\ supported_expr (main_module mods) e /\
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (Append bt e) /\
  call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Append bt e) ==> occurs_abi_decode_target target (main_module mods)) /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `exps` |-> `exps`]
                  stmt_expr_body_pre_main_alloc_mods) >>
  fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
     alloc_limits_stmt_def, int_calls_stmt_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED

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
  rpt strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `s` |-> `Append (TopLevelNameTarget nid) e`]
          body_inv_stmt_expr_pre_singleton) >>
  simp[supported_stmt_expr_exists_def] >>
  disch_then irule >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                   `ctx` |-> `ctx`, `bt` |-> `TopLevelNameTarget nid`] body_append_expr_pre_mods) >>
  simp[main_module_def, ALOOKUP_def]
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

