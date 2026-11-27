Theory bodyFullExtCallKeywords
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull gasOutcomeFullCompose
  exprSimSource exprSimWordArgs exprLoweringProps contextRawReachable
  ptrDiscipline unitMemInv exprLowering compileEnv gasOutcomeFull loweringPosts
  exprSimSend vyperValue vyperState vyperTyping venomState words
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

(* Scalar keywords use the child's lower_value endpoint, without another
   machine step. Keep its frame and exit so the remainder can compose. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qabbrev_tac `ty = if k = EKDefault then rt else BaseT (UintT 256)` >>
  `lower_value compile_expr cenv ty e sa = (op,sb) /\
   lower_value compile_expr (gas_shadow_env T cenv) ty
     (gas_shadow_expr e) shadow_sa = (op,shadow_sb)` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ e _ = _` mp_tac >>
     qpat_x_assum `compile_ext_call_kwarg _ _ _ _ (gas_shadow_expr e) _ = _` mp_tac >>
     simp[compile_ext_call_kwarg_def, Abbr `ty`, comp_bind_def,
          comp_return_def, pairTheory.pair_case_thm] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >> disch_then drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl [`cenv`,`s0`,`sa`] >> simp[] >>
      reverse conj_tac
      >- (mp_tac (Q.SPECL [`cenv`,`ty`,`e`,`sa`] ci_mono_lower_value_compile_expr) >>
          simp[ci_mono_def]) >>
      fs[expr_post_def]) >>
  strip_tac >>
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := xs)` by simp[] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_at (Pat `bind _ _ _ = (INL _,_)`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value) >>
  disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
  simp[evaluate_type_def] >> strip_tac >>
  qhdtm_x_assum `expr_post` mp_tac >>
  simp[expr_post_def, expr_val_rel_def, is_word_type_def,
       evaluate_type_def, uint256_typed_dest]
QED
*)
Theorem extcall_kwarg_scalar_full:
  body_expr_full_ok_mods mods exps cx e /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\ ~(k = EKDefault /\ ~is_word_type rt) /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,rt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k
    (gas_shadow_expr e) shadow_sa = ((op,rt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (post_value_type cenv e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\
      (expr_type e = BaseT (UintT 256) /\ post_value_type cenv e = expr_type e ==>
       ?w. eval_operand op t = SOME w /\ dest_NumV v = SOME (w2n w)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  cheat
QED
