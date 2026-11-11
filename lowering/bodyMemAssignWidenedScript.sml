(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a local held in memory, assigned a value that widens other than as a
   bytestring (S1's body_assign_widened_aggregate_call, RESIDUAL #767). *)
Theory bodyMemAssignWidened
Ancestors
  bodyMemoryPreds widenedMemoryStaging typedNormalizeRankPathMem
  widenedAssignValueParts widenedLocalRuntimeMem widenedAssignmentPreparationMem widenedAssignContinuationMem widenedAssignmentIntegrationMem

Theorem body_assign_widened_aggregate_call_mem:
  !cx id e ty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED
