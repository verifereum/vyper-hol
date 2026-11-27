(* The shared positional run at the paired RaiseCustom compiler cuts. *)
Theory bodyCustomErrorPositionalMods
Ancestors
  bodyExtPosListRunMods bodyFullPredsMods exprSimFullBundleProps
  gasShadowCompilePure exprSimHypsDefs loweringPosts list
Libs horizonTypeLib

Theorem custom_error_positional_outcome_mods:
  body_exprs_full_ok_mods mods exps cx args /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  (!e. MEM e args ==> expr_body_pre_mods mods cenv cx env e es) /\
  compile_ext_call_args compile_expr cenv []
    (MAP (lowered_value_type cenv) args) args sa = (saved,se) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) []
    (MAP (lowered_value_type cenv) args) (MAP gas_shadow_expr args) sha = (saved,te) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,se,sha,te) /\
  local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
    (extcall_positional_post_mods F mods DF lo d ctx func cenv cx env
      [] args saved sa se es s0 G0 tn0)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_then strip_assume_tac expr_sim_full_code_fields >>
  `!e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st ==>
    expr_body_pre_mods mods cenv cx env e st` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum (drule_then mp_tac) >> simp[expr_body_pre_mods_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  irule ext_pos_list_run_mods >> asm_rewrite_tac[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  rpt conj_tac
  >- (qexistsl_tac [`shadow_func`,`sha`,`te`] >> simp[])
  >- (qexists_tac `exps` >> simp[])
  >- (qexistsl_tac [`src`,`tops`] >> simp[])
QED
