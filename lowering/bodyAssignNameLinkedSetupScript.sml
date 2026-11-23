(* Static and RHS facts common to the linked local assignment routes. *)
Theory bodyAssignNameLinkedSetup
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyActiveStmtCallsMods bodyWriteOperandMods
  bodyInvModuleProps bodyInvCodeProps bodyInvMetadataProps bodyCallSupport
  exprBodyPreProps exprSimSource exprSimHypsDefs typedMemoryCopy valueEncodingProps bodySim
  vyperTypeSystem vyperTypeEnv vyperTypeArgFits vyperTypeEvalCaseProofs
  gasShadowCompileStmtHelpers gasShadowState gasShadow compileEnv
  supportedStmtTraverse finite_map list pair

(* Exactly the statement premises, retaining the active module and the
   retirement frame even though the setup itself does not consume the latter. *)
Definition linked_assign_name_context_mods_def:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es <=>
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
           IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
           IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty
End

Theorem assign_name_typing:
  type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' ==>
  env' = env /\ well_typed_expr env e /\ assignable_type env.type_defs (expr_type e) /\
  ?ty. FLOOKUP env.var_types id = SOME ty /\ FLOOKUP env.var_assignable id = SOME T /\
       type_widens_to env.type_defs (expr_type e) ty
Proof
  simp[Once type_stmt_def, AllCaseEqs(), atarget_accepts_def] >> strip_tac >>
  Cases_on `type_place_target env (NameTarget id)` >> gvs[] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >>
  gvs[type_place_target_NameTarget]
QED

Theorem assign_name_memory_bytes_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes cenv ty = type_memory_size tv
Proof
  strip_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  fs[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem assign_name_local_layout_mods:
  expr_sim_inv_mods mods cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\ assignable_type (get_tenv cx) ty ==>
  cenv.ce_var_type id = SOME ty /\
  (?p cap. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap)) /\
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
       type_memory_bytes cenv ty = type_memory_size tv /\
       0 < type_memory_bytes cenv ty /\ type_memory_bytes cenv ty < 2 ** 64
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all env_consistent_var_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> disch_then (qx_choose_then `tv` assume_tac) >>
  drule_all_then assume_tac assign_name_memory_bytes_mods >>
  `0 < type_memory_size tv` by
    (irule (cj 1 type_memory_size_pos) >>
     drule_all_then ACCEPT_TAC assignable_type_slot_size_pos) >>
  fs[expr_sim_inv_mods_def, locals_alloc_ok_def] >> metis_tac[]
QED

Theorem linked_assign_name_setup_mods:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es /\
  body_expr_full_ok_mods mods exps cx e ==>
  expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
  ?ty. FLOOKUP env.var_types id = SOME ty /\ FLOOKUP env.var_assignable id = SOME T /\
       cenv.ce_var_type id = SOME ty /\
       type_widens_to (get_tenv cx) (expr_type e) ty /\
       (?p cap. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap)) /\
       ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
            type_memory_bytes cenv ty = type_memory_size tv /\
            0 < type_memory_bytes cenv ty /\ type_memory_bytes cenv ty < 2 ** 64
Proof
  rewrite_tac[linked_assign_name_context_mods_def] >> strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e))` by
    (drule_all_then strip_assume_tac active_stmt_calls_resolve_mods >>
     qpat_assum `!bindings s ret env'. _ ==> EVERY _ (int_calls_stmt s)` irule >>
     conj_tac >- (qexistsl_tac [`env'`, `ret_ty`] >> simp[]) >>
     qexists_tac `bindings` >> simp[]) >>
  drule_all_then assume_tac assign_rhs_body_pre_linked >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     first_assum irule >> metis_tac[]) >>
  drule_then strip_assume_tac assign_name_typing >>
  drule_then (assume_tac o MATCH_MP env_consistent_type_defs_get_tenv) expr_sim_inv_mods_env >>
  `assignable_type (get_tenv cx) ty` by metis_tac[type_widens_to_assignable_type] >>
  drule_all_then strip_assume_tac assign_name_local_layout_mods >>
  fs[]
QED

Theorem assign_name_shadow_raw_rhs_mods:
  gas_shadow_state sa shadow_sa /\ compile_expr cenv ty e sa = (vv,sm) ==>
  ?shadow_sm.
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
      (vv,shadow_sm) /\ gas_shadow_state sm shadow_sm
Proof
  strip_tac >>
  mp_tac (Q.INST [`sd` |-> `T`] gas_shadow_stmt_compile_expr_env) >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa` >>
  simp[]
QED

Theorem assign_name_shadow_value_rhs_mods:
  gas_shadow_state sa shadow_sa /\ lower_value compile_expr cenv ty e sa = (opr,sm) ==>
  ?shadow_sm.
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
      (opr,shadow_sm) /\ gas_shadow_state sm shadow_sm
Proof
  strip_tac >>
  mp_tac (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env) >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa` >>
  simp[]
QED
