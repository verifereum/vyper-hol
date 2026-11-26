(* The real and shadow cuts and the forced operand run for Abs. *)
Theory bodyWordAbsPrefixMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprBodyPreProps exprSimHypsDefs
  exprSimUnopProps exprSimUnopComposeProps exprWordOperand exprLoweringProps exprSimSource
  gasShadowCompileStmtHelpers gasShadowState gasShadow gasOutcomeFullMods gasContext
  loweringPosts exprSimDefs exprSimMemDefs bodyPtrDefs fragExec compileEnv
  exprLowering stmtSimDefs vyperTypeInvariants vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperAST vyperStorageFootprint venomState

Theorem abs_word_operand_shape[local]:
  lower_value compile_expr cenv ty e sa = (x,s1) /\
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) ==>
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
  drule_all_then strip_assume_tac lower_value_word_shape >> simp[]
QED

Theorem abs_lower_cuts[local]:
  lower_value compile_expr cenv ty (Builtin ann Abs [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann Abs [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x s1 shadow_s1.
    lower_value compile_expr cenv ty e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e)
      shadow_sa = (x,shadow_s1) /\
    gas_shadow_state s1 shadow_s1 /\ compile_builtin_abs x s1 = (op,sb) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func
Proof
  strip_tac >> drule_then strip_assume_tac lower_value_abs >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  disch_then (strip_assume_tac o MATCH_MP lower_value_abs) >>
  rename1 `compile_builtin_abs shadow_x shadow_s1 = (op,shadow_sb)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e)
       (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `shadow_x = x` SUBST_ALL_TAC >>
  qpat_assum `lower_value compile_expr cenv ty e sa = _`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = (_,shadow_s1)`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  `cs_extends s1 sb` by metis_tac[straight_fresh_cs_extends,straight_fresh_abs] >>
  `cs_extends shadow_s1 shadow_sb` by
    metis_tac[straight_fresh_cs_extends,straight_fresh_abs] >>
  qexistsl_tac [`x`,`s1`,`shadow_s1`] >> simp[] >>
  metis_tac[fn_has_code_split]
QED

Theorem word_abs_prefix_run_mods:
  expr_type e = BaseT (IntT 256) /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  lower_value compile_expr cenv ty (Builtin (BaseT (IntT 256)) Abs [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin (BaseT (IntT 256)) Abs [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  gas_admissible (bind (eval_expr cx (Builtin (BaseT (IntT 256)) Abs [e]))
    (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     immutable_frame_mods func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x s1 shadow_s1.
    lower_value compile_expr cenv ty e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e)
      shadow_sa = (x,shadow_s1) /\
    gas_shadow_state s1 shadow_s1 /\ compile_builtin_abs x s1 = (op,sb) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    fn_has_code s1 sb func /\
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?v. res = INL v /\
        expr_post_mods H ctx func cenv cx e es sa s1 s0 ee v x t /\
        expr_store_bound cx (post_value_type cenv e) v x t /\
        t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
        (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all_then strip_assume_tac abs_lower_cuts >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac abs_word_operand_shape >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >>
     qexistsl_tac [`BaseT (IntT 256)`,`Abs`] >>
     simp[builtin_args_length_ok_def,precompile_builtin_def,is_self_codesize_def]) >>
  qexistsl_tac [`x`,`s1`,`shadow_s1`] >>
  reverse (rpt conj_tac)
  >- (qpat_x_assum `expr_sim_full_mods _ _ _ _ e es`
       (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac o
        PURE_REWRITE_RULE [expr_sim_full_mods_def]) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
