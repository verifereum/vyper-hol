(* HELD (#767): a memory-backed declaration of an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise).
   The memory twin of bodySimDeclCases' body_annassign_widened_aggregate_call,
   admitted as that one is. *)
Theory bodyMemAnnAssignWidened
Ancestors
  bodyMemoryPreds widenedLocalContinuationMem widenedLocalOutcomeMem
  widenedAssignValueParts widenedLocalRuntimeMem
  bodyExprPreFacts supportedStmtTraverse supportedStmts vyperTypeInvariants
  vyperTypeSystem vyperTypeExprResult vyperTyping bodySim exprSimHypsDefs
  gasContext supportedTypes vyperInterpreter vyperTypeCallGraph vyperState
  bodyDeclMemoryCounted bodyDeclCopyMemory stmtSimDeclCompose stmtSimDecl
  stmtSimDeclMem exprLoweringProps exprSimProps stmtSimProps stmtSimDefs
  bodySimDeclCases
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
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
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
  rpt gen_tac >> strip_tac >>
  `supported_expr tops e /\ supported_copy_types typ (expr_type e)` by
    gvs[supported_stmt_def] >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >> simp[lift_option_type_def, return_def]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  suspend "compile"
QED

Resume body_annassign_widened_aggregate_call_mem[compile]:
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by
    (rpt strip_tac >> `FLOOKUP cenv.ce_vars id = NONE` by
       (irule declared_name_unbound >> metis_tac[]) >> gvs[]) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id typ sa = (c, st)` >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `expr_body_pre c cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_mem ctx func c cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  suspend "parts"
QED

Resume body_annassign_widened_aggregate_call_mem[parts]:
  cheat
QED

Finalise body_annassign_widened_aggregate_call_mem
