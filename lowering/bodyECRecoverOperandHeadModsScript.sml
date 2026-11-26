(* Land one forced ECRecover operand on its real and shadow compiler cut. *)
Theory bodyECRecoverOperandHeadMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach exprSimFullBundleProps
  gasOutcomeFullPostMods gasOutcomeFullPostPathMods fragExec
Libs monadsyntax

val head_post = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:value + exception) (mid:evaluation_state)
    (G:(string |-> num # num)) (tn:taint) (t:venom_state). ?v:value. res = INL v /\
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
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val head_exit = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:value + exception) mid (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx mid res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem ecrecover_operand_head_run_mods:
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
    (\H res mid G tn t. (^head_post) H res mid G tn t /\
       ~t.vs_halted /\ mid.gas_obs = [] /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u))
    ^head_exit
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (first_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  fs[expr_sim_full_code_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (^head_post) (^head_exit)` by
    (qhdtm_x_assum `expr_sim_full_mods`
       (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac) >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res mid G tn t. (^head_post) H res mid G tn t /\
    (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)`,
    `^head_exit`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qexists_tac `^head_post` >> BETA_TAC >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> rpt strip_tac >>
      drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >> rpt strip_tac >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!fn inst u. frag_reachable _ _ _ fn inst u ==> dalloca_fmp_headroom inst u`
    (drule_at Any) >> simp[]
QED
