(* HELD (#767): a memory-backed declaration of an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise).
   The memory twin of bodySimDeclCases' body_annassign_widened_aggregate_call,
   admitted as that one is. *)
Theory bodyMemAnnAssignWidened
Ancestors
  bodyMemoryPreds widenedMemoryStaging typedNormalizeScalarEntryPathMem
Libs
  monadsyntax

Theorem body_annassign_widened_aggregate_call_mem:
  !d cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED
