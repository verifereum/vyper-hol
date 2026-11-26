(* Reassociate the linked head post for the operand-list bind. *)
Theory bodyECRecoverOperandHeadAdapterMods
Ancestors bodyECRecoverOperandHeadMods gasOutcomeFullPostMods
Libs monadsyntax

Theorem ecrecover_operand_head_run_mods_normalized:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\
  lower_value compile_expr cenv ty e sa = (x,s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid G tn t. ?v:value. res = INL v /\
       expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
       expr_store_bound cx (post_value_type cenv e) v x t /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\
       alloca_history func t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
       ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
       ~t.vs_halted /\ mid.gas_obs = [] /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u))
    (\H (res:value + exception) mid (gt:(string |-> num # num) # taint) r.
       expr_exit res r /\ halt_exit H cx mid res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_tac >> mp_tac (BETA_RULE ecrecover_operand_head_run_mods) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `v` >> simp[] >>
  first_assum ACCEPT_TAC
QED
