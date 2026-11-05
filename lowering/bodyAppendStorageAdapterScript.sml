(* Body-side discharge for primitive storage Append. *)
Theory bodyAppendStorageAdapter
Ancestors
  stmtSimDefs
  bodyAppendStorageFacts bodyExprPreFacts stmtSimAppendStorageCompose
  stmtSimAssignStorage bodySim exprSimHyps supportedStmts supportedStmtTraverse
  vyperStorageLayoutSafety vyperTypeSystem vyperTypeValues compileEnv
  vyperTypeCallGraph vyperState vyperInterpreter
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  supportedDecls supportedTypes vyperValue bodyStorageMetadata
Libs
  monadsyntax

Theorem body_append_expr_pre:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  cheat
QED

Theorem body_append_word_encoding:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) ==>
  encode_value tv v = SOME [(0,typed_val_to_w256 tv v)]
Proof
  cheat
QED

Theorem stmt_frag_storage_rel_discharge[local]:
  ((storage_vars_rel cenv cx /\ transient_vars_rel cenv cx) ==>
    stmt_frag ctx func cx lctx RetQ cenv m source es) ==>
  stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  cheat
QED

Theorem body_append_storage_fragment:
  (!s p t. eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,t) ==>
             body_expr_ok cx e) /\
  body_inv tops ctx cenv cx /\ supported_storage_dynamic_array tops (src,id) /\
  supported_expr tops e /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget (src,id)) e)) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget (src,id)) e))
      (eval_stmt cx (Append (TopLevelNameTarget (src,id)) e)) es
Proof
  cheat
QED
