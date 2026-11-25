(* Compose calldata word-list requests up to the prepared callback. *)
Theory s1PrefixRawCallCalldataWords
Ancestors
  s1PrefixWordArgs s1PrefixCompose s1PrefixPreds s1PrefixDefs s1PrefixFrame
  s1PrefixOfVV s1PrefixProps bodyFullWordArgs bodyFullPreds bodySimFull
  bodyFullIfExpReach exprSimSource exprSimWordArgs exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState loweringPosts loweringShapeDefs
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  fragExec list pair s1PrefixRawCallCalldataWordsReplay

Theorem raw_call_calldata_words_prefix_by:
  body_exprs_full_ok cx (a::kws) /\ body_exprs_prefix_ok cx (a::kws) /\
  body_inv tops ctx cenv cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e ee. MEM e (a::kws) /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
  lower_word_args cenv (K (BaseT (UintT 256))) (a::kws) sa =
    (addr::xs,s2) /\
  lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
    (MAP gas_shadow_expr (a::kws)) shadow_sa = (addr::xs,shadow_s2) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state s2 shadow_s2 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa s2 func /\ fn_has_code shadow_sa shadow_s2 shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  (!v. requests_outcomes_frame (k v)) /\
  (!marksK vs esK tk GK tnK.
    (!tail. eval_exprs cx (a::kws)
      (es with gas_obs := gas_explicit marksK s0.vs_gas_readings ++ tail) =
      (INL vs,esK with gas_obs := tail)) /\
    storage_trace_domain cx st0 esK.storage_trace /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      typed_args_post H ctx func cenv cx es sa s0 esK (a::kws) (addr::xs) vs tk /\
      tk.vs_current_bb = s2.cs_current_bb /\
      tk.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func tk /\ s0.vs_alloca_next <= tk.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK /\
      EVERY (\x. op_taint tnK x = {}) (addr::xs)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (k vs) (esK,tk,GK,tnK)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx (a::kws)) k) (es,s0,G0,tn0)
Proof
  strip_tac >> irule raw_call_calldata_words_prefix_replay_by >>
  qpat_assum `lower_word_args cenv (K _) (a::kws) sa = _` (irule_at Any) >>
  qpat_assum `lower_word_args _ (K _) (MAP gas_shadow_expr _) _ = _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
  qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
  qx_genl_tac [`marksK`,`vs`,`esK`,`tk`,`GK`,`tnK`] >> strip_tac >>
  qpat_assum `!marksK vs esK tk GK tnK. _ ==> gas_prefix_full _ _ _ _ _`
    (qspecl_then [`marksK`,`vs`,`esK`,`tk`,`GK`,`tnK`] mp_tac) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED
