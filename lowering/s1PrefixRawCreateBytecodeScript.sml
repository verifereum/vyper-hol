(* Requests in the bytecode expression precede the silent CREATE snapshot. *)
Theory s1PrefixRawCreateBytecode
Ancestors
  s1PrefixPreds s1PrefixOfVV s1PrefixDefs exprSimSource exprSimMemorySource
  exprSimHypsDefs exprSimDefs exprLowering gasContext gasShadow gasShadowState
  exprLoweringProps loweringPosts bodyPtrDefs allocLimits vyperStorageFootprint
  vyperInterpreter vyperState vyperAST compileEnv list

Theorem raw_create_bytecode_operand_prefix:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env code es /\ body_expr_prefix_ok cx code /\
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  compile_expr (gas_shadow_env T cenv) (expr_type code) (gas_shadow_expr code) sh = (vv,sha) /\
  gas_shadow_state sa sh /\ gas_shadow_state a sha /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa a func /\ fn_has_code sh sha shadow_func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx code) (read_result cx)) (es,s,G,tn)
Proof
  strip_tac >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type code) code es` by
    metis_tac[CONJUNCT1 body_expr_prefix_ok_def] >>
  `expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type code) code es (st0,sa,a,sh,sha,vv,s,G,tn)` by
    (simp[expr_vv_sim_full_pre_def] >>
     metis_tac[expr_body_pre_gas_admissible, forced_expr_admissible_raw]) >>
  rewrite_tac[gas_prefix_full_bind_read_result] >>
  qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (drule_then ACCEPT_TAC o REWRITE_RULE[expr_vv_sim_prefix_def])
QED
