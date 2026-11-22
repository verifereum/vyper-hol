(* Request-prefix companion to bodyFullAnnAssignWord. *)
Theory s1PrefixAnnAssignWord
Ancestors
  s1PrefixPreds bodyFullAnnAssignWord s1PrefixDefs

Theorem annassign_word_prefix_execution_sep:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\
  fn_has_code shadow_sa shadow_sf shadow_func /\
  (ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_stmt cx (AnnAssign id (expr_type e) e))
      (es,s0,G0,tn0)
Proof
  cheat
QED

Theorem annassign_word_prefix_execution:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\
  fn_has_code shadow_sa shadow_sf shadow_func /\
  ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_stmt cx (AnnAssign id (expr_type e) e))
      (es,s0,G0,tn0)
Proof
  cheat
QED
