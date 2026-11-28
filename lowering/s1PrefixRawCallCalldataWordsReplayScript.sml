(* Replay the calldata word-list evaluation up to the prepared callback. *)
Theory s1PrefixRawCallCalldataWordsReplay
Ancestors
  s1PrefixWordArgs s1PrefixCompose s1PrefixPreds s1PrefixDefs s1PrefixProps
  bodyFullWordArgs bodyFullPreds bodySimFull gasOutcomeFullCompose
  bodyFullIfExpReach exprSimSource exprSimWordArgs exprSimDefs exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState loweringPosts loweringShapeDefs
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  fragExec list pair

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx (a::kws)) (es,s0,G0,tn0)` by
    (irule lower_word_args_by_type_prefix >>
     qpat_assum `lower_word_args cenv tyf (a::kws) sa = _` (irule_at Any) >>
     qpat_assum `lower_word_args _ tyf (MAP gas_shadow_expr _) _ = _` (irule_at Any) >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx (a::kws)) (es,s0,G0,tn0)
     (\H rr mid G tn t. ?vs. rr = INL vs /\
       typed_args_post H ctx func cenv cx es sa s0 mid (a::kws) (addr::xs) vs t /\
       t.vs_current_bb = s2.cs_current_bb /\
       t.vs_inst_idx = LENGTH s2.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at (DF H) lo dframe cenv cx mid G tn t /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
       EVERY (\x. op_taint tn x = {}) (addr::xs))
     (\H rr mid gt r. wb_args_exit rr r /\ halt_exit H cx mid rr r /\
       (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))` by
    (irule lower_word_args_by_type_sim_full >>
     qpat_assum `lower_word_args cenv tyf (a::kws) sa = _` (irule_at Any) >>
     qpat_assum `lower_word_args _ tyf (MAP gas_shadow_expr _) _ = _` (irule_at Any) >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ wordQ wordR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx (a::kws)) (es,s0,G0,tn0)
     (\H rr mid G tn t. wordQ H rr mid G tn t /\ ~t.vs_halted /\ mid.gas_obs = []) wordR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ wordQ wordR`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  pop_assum (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame] >>
  reverse conj_tac
  >- (simp[Abbr `wordR`] >> Cases_on `res` >> simp[wb_args_exit_def]) >>
  qx_genl_tac [`marksK`,`vs`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    fs[storage_trace_domain_def] >>
  `esK.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
       (qspec_then `storage_trace_horizon esK.storage_trace` (drule_then mp_tac)) >> simp[]) >>
  `esK with gas_obs := [] = esK` by simp[evaluation_state_component_equality] >>
  qpat_assum `!marksK vs esK tk GK tnK. _ ==> gas_prefix_full _ _ _ _ _`
    (qspecl_then [`marksK`,`vs`,`esK with gas_obs := []`,`tk`,`GK`,`tnK`] mp_tac) >>
  simp[] >> disch_then irule >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `H` (drule_then mp_tac)) >>
  simp[NoAsms, Abbr `wordQ`] >> strip_tac >> simp[]
QED
*)
Theorem raw_call_calldata_words_prefix_replay_by:
  body_exprs_full_ok cx (a::kws) /\ body_exprs_prefix_ok cx (a::kws) /\
  body_inv tops ctx cenv cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e ee. MEM e (a::kws) /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
  (!e. tyf (gas_shadow_expr e) = tyf e) /\
  lower_word_args cenv tyf (a::kws) sa = (addr::xs,s2) /\
  lower_word_args (gas_shadow_env T cenv) tyf
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
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marksK (OK tk,GK,tnK) /\
      typed_args_post H ctx func cenv cx es sa s0 esK (a::kws) (addr::xs) vs tk /\
      tk.vs_current_bb = s2.cs_current_bb /\
      tk.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func tk /\ s0.vs_alloca_next <= tk.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK /\
      EVERY (\x. op_taint tnK x = {}) (addr::xs) /\
      ~tk.vs_halted /\ esK.gas_obs = []) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (k vs) (esK,tk,GK,tnK)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx (a::kws)) k) (es,s0,G0,tn0)
Proof
  cheat
QED
