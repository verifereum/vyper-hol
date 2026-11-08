(* Source typing and allocation facts for the supported local-memory wrapper. *)
Theory assignBasePtrLocalBodyFacts
Ancestors bodySim bodyExprPreFacts memoryLocalRhsProps exprSimHyps exprSimHypsDefs
  exprSimDefs exprSimAggregateLayout vyperTypeArgFits supportedStmtTraverse
  supportedStmts supportedExprs vyperTypeSystem vyperTypeEnv vyperTypeCallGraph
  vyperTypeInvariants gasContext finite_map list compileEnv

Theorem assign_base_local_rhs_pre:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >> Cases_on `asg` >> gvs[]) >>
  simp[] >> drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem assign_base_local_memory_bytes_pos:
  !cenv cx env es ret_ty id e env' ty.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty ==>
    0 < type_memory_bytes cenv ty
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `assignable_type env.type_defs ty` by
    (gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
     Cases_on `type_place_target env (NameTarget id)` >> gvs[] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[type_place_target_NameTarget] >> metis_tac[type_widens_to_assignable_type]) >>
  irule expr_sim_inv_memory_bytes_pos >> metis_tac[]
QED

Theorem assign_base_local_memory_sizes:
  !cenv cx env es ret_ty id e env' ty tops.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty /\
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    0 < type_memory_bytes cenv ty /\ type_memory_bytes cenv ty < 2 ** 64 /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_memory_bytes cenv ty` by metis_tac[assign_base_local_memory_bytes_pos] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[memory_rhs_destination_bound]
QED
