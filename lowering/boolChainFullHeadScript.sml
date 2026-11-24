(* A reached Boolean operand at the joint judgment. *)
Theory boolChainFullHead
Ancestors
  bodyFullSimProjection gasOutcomeFullCompose exprSimSource exprSimWordArgs
  bodyPtrDefs loweringPosts compileEnv vyperTypeValues vyperValue
  vyperInterpreter vyperState venomState bodySimFull loweringSlice valueEncoding
  venomExecSemantics wordArgsPtr exprSimProps

Theorem bool_chain_full_head:
  body_expr_full_ok cx e /\ expr_type e = BaseT BoolT /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sc) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr e)
    shadow_sa = (op, shadow_sc) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sc shadow_sc /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sc func /\ fn_has_code shadow_sa shadow_sc shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' u. ?b.
      res = INL (BoolV b) /\ expr_post H ctx func cenv cx e es sa sc s ee (BoolV b) op u /\
      eval_operand op u = SOME (if b then 1w else 0w) /\
      u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
      ptr_val_ok cx (BaseT BoolT) (BoolV b) op G' tn' u /\
      ghost_kept_at lo cenv es sa G tn s G' tn')
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT BoolT) e es` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`op`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := xs)` by simp[] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value) >>
  simp[evaluate_type_def] >> disch_then (strip_assume_tac o MATCH_MP value_has_type_BoolTV) >>
  gvs[] >> drule expr_post_word_operand >>
  Cases_on `b` >> simp[evaluate_type_def, word_value_def, val_to_w256_def,
                          bool_to_word_def, is_word_type_def]
QED

(* Extend the entry's accumulated frame with the head's local frame. *)
Theorem bool_chain_full_accumulate:
  expr_type root = BaseT BoolT /\ (~expr_has_effect root ==> ~expr_has_effect e) /\
  local_ptrs_reserved cenv sa0 /\ sa0.cs_next_var <= sa.cs_next_var /\
  sa0.cs_next_id <= sa.cs_next_id /\
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es0 s0 /\
  wb_frame cenv es0 es sa0 s0 s /\
  (~expr_has_effect root ==> pure_frame cenv func es0 sa0 s0 s) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  expr_post H ctx func cenv cx e es sa sc s ee (BoolV b) op u /\
  eval_operand op u = SOME (if b then 1w else 0w) /\
  ghost_kept_at lo cenv es sa G tn s G' tn' ==>
  expr_post H ctx func cenv cx root es0 sa0 sc s0 ee (BoolV b) op u /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `MAP FDOM es0.scopes = MAP FDOM es.scopes` by
    fs[wb_frame_def, locals_kept_def] >>
  `wb_frame cenv es ee sa s u` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es0 ee sa0 s0 u` by metis_tac[wb_frame_trans] >>
  `~expr_has_effect root ==> pure_frame cenv func es0 sa0 s0 u` by
    (strip_tac >>
     `pure_frame cenv func es sa s u` by metis_tac[expr_post_pure_frame] >>
     irule pure_frame_trans >> simp[] >> qexistsl_tac [`es`,`sa`,`s`] >> fs[wb_frame_def]) >>
  conj_tac
  >- (irule expr_post_word_intro >>
      fs[expr_post_def, is_word_type_def, word_value_def, val_to_w256_def, bool_to_word_def]) >>
  drule_all ghost_kept_at_wb_trans >> simp[]
QED
