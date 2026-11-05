(*
 * Body simulation: Assign to any place, from the body case's hypotheses
 *
 * body_assign_other's hypotheses (the body induction's judgments for e and
 * the target's indices, body_inv, the statement's support and typing) give
 * the premises of stmtSimAssignPlace's roots: the target's typing and
 * widening from type_stmt, target_case from body_base_target_ok, the
 * indices' expr_body_pre from the statement's support, and e's
 * expr_vv_sim from body_expr_ok.  An immutable target is one the
 * constructor writes (immutable_deploy_assign_case); at run time it has
 * no place.
 *
 * TOP-LEVEL:
 *   body_assign_place_case — t = e, when e's lowered value has e's type
 *     (or a bytestring type it fits)
 *)

Theory bodyAssignPlace
Ancestors
  stmtSimAssignPlace bodySim exprSimHypsDefs stmtSimDefs
  targetPlaceSim targetPlaceSimCases supportedStmts supportedTargets
  supportedStmtTraverse supportedProgram bodyExprPreFacts gasContext
  vyperTypeInvariants vyperTypeCallStackSoundness vyperCompiler
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperTypeSystem

Theorem body_assign_place_case:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
                (Assign (BaseTarget t) e) ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED
