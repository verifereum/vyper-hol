(* Memory case of the body induction, assignment to a tuple of locals
   (bodyMemAssignTuple's dispatch): the memory twin of S1's
   body_assign_tuple_locals (bodySimStmtCases). *)
Theory bodyMemAssignTupleLocals
Ancestors
  bodyMemoryPreds

Theorem body_assign_tuple_locals_mem:
  !cx ids e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids /\
    lowered_value_type cenv e = expr_type e ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  cheat
QED
