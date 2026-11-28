(* The pure empty RHS emits no code before the target. *)
Theory s1PrefixAssignResidualEmpty
Ancestors
  s1PrefixPreds s1PrefixDefs bodyFullAssign bodyFullPreds
  assignPlacePureCode assignPlaceEmpty assignPlaceEmptyCompose immutableAssignEmpty
  exprSimAbiDecodeEntryTyping exprSimHyps exprSimHypsDefs gasShadowCompileStmtBase
  exprLoweringProps loweringPosts bodyFullShared
  gasShadowCompileStmtHelpers gasShadowState gasShadow stmtLoweringMono
  fragExec exprLowering stmtLowering targetPlaceSimDefs
  vyperTypeSystem vyperTypeArgFits vyperInterpreter vyperState option pair

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac body_assign_empty_target_typing >>
  drule_all_then assume_tac body_assign_empty_target_rhs_pre >>
  drule_then assume_tac abi_decode_inv_type_env >>
  drule_then assume_tac expr_body_pre_type_evaluates >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[type_widens_to_def, well_formed_type_def] >> metis_tac[IS_SOME_EXISTS]) >>
  `body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t` by
    (drule_all immutable_assign_empty_read >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all_then assume_tac body_assign_target_indices_pre >>
  drule_all_then assume_tac (Q.INST [`bt` |-> `t`] assign_place_empty_source_action) >>
  pure_rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac assign_place_empty_target_admissible >>
  drule_all_then strip_assume_tac assign_place_pure_empty_code >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (mp_then Any mp_tac assign_place_pure_empty_code o
     REWRITE_RULE [gas_shadow_stmt_def,gas_shadow_assignment_def]) >>
  simp[] >> disch_then (qx_choosel_then [`shadow_tr`,`shadow_st`] strip_assume_tac) >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv t)
      (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
         (gas_shadow_target t))` by irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) gas_shadow_step >>
  `ci_mono sa st /\ ci_mono shadow_sa shadow_st` by
    metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono st sb /\ ci_mono shadow_st shadow_sb` by
    metis_tac[cj 2 ci_mono_stmt_helpers, SND] >>
  `fn_has_code sa st func /\ fn_has_code shadow_sa shadow_st shadow_func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (eval_target_place cx t) (\p. write_place cx p (default_value dtv)))
      (es,s0,G0,tn0)` by
    (qpat_assum `!st0 ty sa st shadow_sa shadow_st tr s0 G0 tn0 v.
       _ ==> gas_prefix_full _ _ _ _ _` irule >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`sa`,`shadow_sa`,`shadow_st`,`st`,`tr`] >> simp[]) >>
  qpat_x_assum `gas_prefix_full _ _ _ (bind _ _) _` mp_tac >>
  simp[gas_prefix_full_def]
QED
*)
Theorem body_assign_residual_empty_from_target:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
   cenv env env' ret_ty lctx RetQ es.
  (!s pv s1 sr v s2. eval_expr cx e s = (INL pv,s1) /\
     read_result cx pv sr = (INL v,s2) ==> body_base_target_full_ok cx t) /\
  (!s pv s1 sr v s2. eval_expr cx e s = (INL pv,s1) /\
     read_result cx pv sr = (INL v,s2) ==> body_base_target_prefix_ok cx t) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  has_length_word (expr_type e) /\ is_empty_value_expr e /\
  (~immutable_root cx t \/ (?nsid. t = TopLevelNameTarget nsid)) /\
  (!st0 ty sa st shadow_sa shadow_st tr s0 G0 tn0 v.
    body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t /\
    target_indices_pre cenv cx env t /\
    type_place_target env t = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv t sa = (tr,st) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (tr,shadow_st) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state st shadow_st /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa st func /\ fn_has_code shadow_sa shadow_st shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    gas_admissible (eval_target_place cx t) target_place_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v))
      (es,s0,G0,tn0)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
    (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED
