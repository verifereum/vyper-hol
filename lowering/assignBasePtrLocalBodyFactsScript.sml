(* Source typing and allocation facts for the supported local-memory wrapper. *)
Theory assignBasePtrLocalBodyFacts
Ancestors bodySim bodyExprPreFacts memoryLocalRhsProps exprSimHyps exprSimHypsDefs
  exprSimDefs exprSimAggregateLayout vyperTypeArgFits supportedStmtTraverse supportedExprTraverse
  supportedStmts supportedExprs vyperTypeSystem vyperTypeEnv vyperTypeCallGraph
  vyperTypeInvariants gasContext finite_map list compileEnv
  bodyInvSplit bodyInvCodeProps bodyInvMetadataProps bodySimModsProps compileUnit alist pair
  allocLimitsProps

Theorem main_module_code_and_gate[local]:
  contract_inv mods exps ctx cenv cx ==>
  ALOOKUP mods NONE = SOME (main_module mods) /\
  get_module_code cx NONE = SOME (main_module mods) /\
  supported_program (main_module mods)
Proof
  strip_tac >>
  drule_then (assume_tac o Q.SPEC `NONE`) contract_inv_module_codes >>
  fs[contract_inv_def, main_module_def, optionTheory.IS_SOME_EXISTS] >>
  res_tac
QED

Theorem assign_base_local_rhs_pre_mods:
  !cx id e mods exps src tops bindings ctx cenv env env' ret_ty es ty.
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    ~supported_expr_exists (unallocated_bare_global_root cenv env) e /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target (main_module mods)) /\
    supported_stmt (main_module mods) bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv_mods mods cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr (main_module mods) e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre_mods mods cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr (main_module mods) e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >> Cases_on `asg` >> gvs[]) >>
  drule_all_then strip_assume_tac supported_expr_body_calls_mods >>
  `~supported_expr_exists (const_name_root_mods mods) e` by
    (drule_then assume_tac contract_inv_cenv_modules >>
     drule stmt_exprs_ok_module_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_assignment_exists_def]) >>
  drule_then strip_assume_tac main_module_code_and_gate >>
  `byte_widths_expr e /\ alloc_limits_expr cenv e` by
    (fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        supported_assignment_exists_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     CCONTR_TAC >> fs[] >>
     qpat_x_assum `~supported_expr_exists (\e. ~is_extcode e /\ _) _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >>
     metis_tac[alloc_limits_expr_not_extcode]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    fs[int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
  `(!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
       EXISTS (occurs_abi_decode_target target o SND) mods)` by
    (fs[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
     rpt strip_tac >> simp[EXISTS_MEM] >>
     qexists_tac `(NONE,main_module mods)` >> simp[] >>
     metis_tac[ALOOKUP_MEM]) >>
  drule_then assume_tac contract_inv_type_env >>
  simp[expr_body_pre_mods_def]
QED

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
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  `supported_expr tops e` by fs[supported_stmt_def, supported_assignment_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_assignment_exists_def]) >>
  drule_all_then assume_tac expr_sim_inv_no_unallocated_bare_globals >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by fs[expr_sim_inv_split_def] >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss()) [main_module_def, ALOOKUP_def]
      (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
        (SPEC_ALL assign_base_local_rhs_pre_mods))) >>
  drule_all_then strip_assume_tac bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
  drule_then assume_tac contract_inv_type_env >>
  fs[expr_body_pre_split_def, supported_stmt_expr_exists_def,
     supported_assignment_exists_def, vyperContextTheory.type_env_all_modules_def,
     vyperContextTheory.type_env_def, finite_mapTheory.FUNION_FEMPTY_2]
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
