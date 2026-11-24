(* Static premises for a linked annotated declaration's RHS, before the
   declared name has been installed in the source scopes. *)
Theory bodyAnnCopyDeclaredRhsMods
Ancestors
  bodyFullPredsMods bodySimDeclCases bodyDeclCopyMemory bodyInvariantFrameProps
  bodyInvExecutionProps bodyInvCodeProps bodyInvMetadataProps exprBodyPreProps
  bodyExprPreFacts typedMemoryCopy valueEncodingProps stmtSimProps
  exprSimHypsDefs bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyCallSupport bodySim stmtLowering compileEnv compileUnit exprLowering
  allocLimits supportedStmts vyperValue vyperState vyperContext vyperInterpreter
  vyperAST vyperTypeSystem list
  allocLimitsProps supportedExprTraverse supportedStmtTraverse
  vyperTypeInvariants vyperTypeEvalCaseProofs vyperTypeCallGraph
  finite_map combin option

Theorem ann_copy_declared_inv[local]:
  expr_sim_inv_mods mods cenv cx env es /\ id NOTIN FDOM env.var_types /\
  declare_local cenv id typ sa = (ce,r) /\ cenv.ce_alloca_locals ==>
  expr_sim_inv_mods mods ce cx env es
Proof
  strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  drule_then assume_tac declare_local_var_type >>
  `ce.ce_flag_member_id = cenv.ce_flag_member_id /\
   ce.ce_flag_n_members = cenv.ce_flag_n_members /\
   ce.ce_struct_fields = cenv.ce_struct_fields /\
   ce.ce_hashmap_info = cenv.ce_hashmap_info /\
   ce.ce_module_var_type = cenv.ce_module_var_type /\
   ce.ce_module = cenv.ce_module /\ ce.ce_modules = cenv.ce_modules /\
   ce.ce_module_vars = cenv.ce_module_vars /\
   ce.ce_func_return_type = cenv.ce_func_return_type /\
   ce.ce_is_ctor = cenv.ce_is_ctor /\ ce.ce_method_id = cenv.ce_method_id` by
    (qpat_assum `ce with <| ce_vars := _; ce_var_type := _;
                             ce_dynarray_capacity := _ |> = cenv`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `place_map_tables_agree_on_defined ce env <=>
   place_map_tables_agree_on_defined cenv env` by
    (irule placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >> simp[]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> n <> id` by
    (rpt strip_tac >> gvs[FLOOKUP_DEF]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==>
         ?p sz. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt strip_tac >> `n <> id` by metis_tac[] >> simp[] >> goal_assum drule) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> ce.ce_var_type n = SOME t` by
    (rpt strip_tac >> `n <> id` by metis_tac[] >> simp[APPLY_UPDATE_THM]) >>
  asm_rewrite_tac[expr_sim_inv_mods_def]
QED

Theorem ann_copy_memory_size[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes cenv ty = type_memory_size tv
Proof
  strip_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  fs[expr_sim_inv_mods_def] >> rpt strip_tac >>
  qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
    drule >> simp[]
QED

Theorem ann_copy_entry_layout[local]:
  expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  stmt_exprs_ok cenv (AnnAssign id typ e) ==>
  env.type_defs = get_tenv cx /\ well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) typ /\
  id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\ type_memory_bytes cenv typ < 2 ** 64 /\
  ?dtv. evaluate_type (get_tenv cx) typ = SOME dtv /\
        type_memory_bytes cenv typ = type_memory_size dtv /\
        0 < type_memory_bytes cenv typ
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\ id NOTIN FDOM env.var_types` by
    gvs[Once type_stmt_def, AllCaseEqs()] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> fs[ce_locals_declared_def] >>
     qpat_x_assum `!n l. FLOOKUP cenv.ce_vars n = SOME l ==> _` drule >> simp[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[env_consistent_def, env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `assignable_type (get_tenv cx) typ` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]) >>
  `?dtv. evaluate_type (get_tenv cx) typ = SOME dtv` by
    (drule assignable_type_well_formed >> simp[well_formed_type_def, IS_SOME_EXISTS]) >>
  drule_all_then assume_tac ann_copy_memory_size >>
  `0 < type_slot_size dtv` by (drule_all assignable_type_slot_size_pos >> simp[]) >>
  simp[] >> irule (cj 1 type_memory_size_pos) >> simp[]
QED

Theorem ann_copy_rhs_pre[local]:
  contract_inv mods exps ctx cenv cx /\ supported_expr tops e /\
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (AnnAssign id typ e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AnnAssign id typ e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >> drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  drule_then assume_tac supported_expr_no_evm_run >>
  fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
     alloc_limits_stmt_def, int_calls_stmt_def] >>
  `byte_widths_expr e` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists (\x. ~is_extcode x /\ _) e` mp_tac >>
     simp[] >> irule supported_expr_exists_root >>
     drule alloc_limits_expr_not_extcode >> simp[]) >>
  simp[expr_body_pre_mods_def]
QED

Theorem ann_copy_declared_rhs_mods:
  (!tenv s tyv t. tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s = (INL tyv,t) ==>
     body_expr_full_ok_mods mods exps cx e) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (AnnAssign id typ e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AnnAssign id typ e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (AnnAssign id typ e)) ==>
  cenv.ce_alloca_locals /\ supported_expr tops e /\
  env.type_defs = get_tenv cx /\ well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) typ /\
  id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  0 < type_memory_bytes cenv typ /\ type_memory_bytes cenv typ < 2 ** 64 /\
  ?dtv. evaluate_type (get_tenv cx) typ = SOME dtv /\
        type_memory_bytes cenv typ = type_memory_size dtv /\
        !sa ce r. declare_local cenv id typ sa = (ce,r) ==>
          same_frame cenv ce /\ contract_inv mods exps ctx ce cx /\
          module_body_inv mods src tops ce cx /\
          expr_body_pre_mods mods ce cx env e es /\
          ce.ce_func_return_type = build_func_return_type_mods mods /\
          type_memory_bytes ce typ = type_memory_bytes cenv typ /\
          lowered_value_type ce e = lowered_value_type cenv e /\
          !DF lo d PG func shadow_func.
            expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
              ce cx (expr_type e) e es /\
            expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
              ce cx (expr_type e) e es
Proof
  strip_tac >> drule_all_then strip_assume_tac ann_copy_entry_layout >>
  drule_then assume_tac contract_inv_alloca_locals >>
  `supported_expr tops e` by fs[Once supported_stmt_def] >>
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_assum `!tenv s tyv t. _ ==> body_expr_full_ok_mods _ _ _ _`
       (qspecl_then [`get_tenv cx`,`es`,`dtv`,`es`] mp_tac) >>
     simp[lift_option_type_def, return_def]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `same_frame cenv ce` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  drule_then assume_tac body_invariants_same_frame >>
  `contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx` by simp[] >>
  drule_all_then assume_tac ann_copy_declared_inv >>
  drule_all_then assume_tac annassign_declare_exprs_ok >>
  drule_all_then strip_assume_tac declare_local_memory_types_mem >>
  `ce.ce_module_vars = cenv.ce_module_vars` by
    (qpat_assum `same_frame cenv ce`
       (strip_assume_tac o REWRITE_RULE [same_frame_def]) >>
     qpat_assum `_ = (cenv:compile_env)` (SUBST1_TAC o SYM) >> simp[]) >>
  `unallocated_bare_global_root ce env = unallocated_bare_global_root cenv env` by
    (simp[FUN_EQ_THM] >> Cases >> simp[unallocated_bare_global_root_def]) >>
  `expr_body_pre_mods mods ce cx env e es` by
    (irule ann_copy_rhs_pre >> simp[] >>
     conj_tac >- (qexistsl_tac [`id`,`typ`] >> simp[]) >>
     conj_tac >- (qexists_tac `tops` >> simp[]) >>
     qexistsl_tac [`ctx`,`exps`] >> simp[]) >>
  `ce.ce_func_return_type = build_func_return_type_mods mods` by
    (qpat_assum `contract_inv mods exps ctx ce cx`
      (ACCEPT_TAC o MATCH_MP contract_inv_return_types)) >>
  simp[] >> rpt gen_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_x_assum `!DF lo d PG src tops ctx sc f sf ce env ty es.
                 _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
    (drule_all_then strip_assume_tac) >> simp[]
QED
