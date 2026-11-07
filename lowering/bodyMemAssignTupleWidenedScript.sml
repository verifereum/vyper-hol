(* Memory case of the body induction, tuple assignment (bodyMemAssignTuple's
   dispatch): a right-hand side whose lowered type is not its type (an
   internal call whose return type the call's type widens).  HELD with S1's
   body_assign_tuple_widened_call (bodySimStmtCases), still admitted there. *)
Theory bodyMemAssignTupleWidened
Ancestors
  bodyMemoryPreds

Theorem body_assign_tuple_widened_call_mem:
  !cx gs e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\
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
    lowered_value_type cenv e <> expr_type e ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED
