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

(* Intuition (a statement check's derivation; ignore if unhelpful):
   - typing: type_stmt_def's Assign case with atarget_accepts_def on
     BaseTarget gives type_place_target env t = SOME (Type dty), the
     widening and assignable_type.
   - target_case: an induction on t gives body_base_target_ok cx t /\
     body_inv ==> target_idx_case F ctx func cenv cx t (body_expr_ok with
     body_inv is expr_sim_case F / expr_vv_case F), then target_case_all.
   - immutable_root: the only supported immutable target is a bare
     TopLevelNameTarget (NONE,n) with supported_immutable_type; every other
     supported root has a storage/transient or hashmap declaration.  At run
     time bare_global_assignable is empty (env_context_consistent in
     expr_sim_inv), so type_place_target is NONE; in deploy it gives the
     immutable's type, for immutable_deploy_assign_case.
   - target_indices_pre and e's expr_body_pre: stmt_expr_body_pre (as
     body_assign_tuple_rhs_pre does it), with int_calls_stmt of Assign =
     int_calls_target t ++ int_calls_expr e, stmt_exprs_ok's
     supported_target_exists for the keys, and the ABI coverage premise
     with cx_tops_module.
   - CapMcopy: bodySimStmtCases' [local] body_inv_mcopy's proof;
     acyclic_struct_metadata: body_inv_def. *)
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
