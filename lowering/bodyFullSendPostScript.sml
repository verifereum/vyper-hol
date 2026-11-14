(* The joint send suffix preserves the caller's frame and allocation history. *)
Theory bodyFullSendPost
Ancestors
  bodyFullSendTail bodyFullShared allocaHistory sendSourceFrame
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr fragGasEmitCtrl
  exprSendPtr exprSimSend bodyPtrDefs exprLoweringProps loweringPosts
  loweringStateRelDefs localPtrsProps compileEnv venomMemProofs ghostPcTransportPtr
  venomExecProofs venomExecSemantics venomState venomInst list

Theorem send_tail_path_full[local]:
  expr_has_effect e /\
  emit_op CALL [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] sm = (success,s3) /\
  emit_void ASSERT [success] s3 = (void,sb) /\ fn_has_code sm sb fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
     stmt_state_rel H ctx fn cenv cx es1 s /\
     storage_well_formed_on cx es' (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es1 G tn s) /\
  wb_frame cenv es es1 sa s0 s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
      read_result cx tv od) es1 = (res,es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?G' tn' r. !H. valid_horizon cx st0 H es'.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn') /\
    ((?z. r = OK z /\ res = INL NoneV /\
      expr_post H ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z /\
      ghost_inv_at (DF H) lo d cenv cx es' G' tn' z /\
      ghost_kept_at lo cenv es1 sm G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn z /\ z.vs_alloca_next = s.vs_alloca_next) \/
     (exit_result r /\ expr_exit res r))
Proof
  strip_tac >>
  reverse (Cases_on `?H0. valid_horizon cx st0 H0 es'.storage_trace`)
  >- (qexistsl_tac [`G`,`tn`,`ARB`] >> metis_tac[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  drule_all call_assert_code_lookup >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `~not_fresh_at sm out /\ ~not_fresh_at sa out` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id CALL
    [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w] [out]` >>
  `inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
   inst.inst_operands = [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w] /\
   get_instruction bb s.vs_inst_idx = SOME inst /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[Abbr `inst`,mk_inst_def] >>
  `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
    (drule eval_send_read >> strip_tac >>
     drule vyperCallOutcomeFrameTheory.eval_send_preserves_non_accounts >> simp[]) >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es1 s /\ stor_taint_ok_at (DF H) tn s` by
    (rpt strip_tac >> res_tac >> fs[ghost_inv_at_def]) >>
  `allocas_from lo s` by
    (res_tac >> fs[ghost_inv_at_def]) >>
  drule_all send_read_checked_tail_full_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  gvs[] >- suspend "normal" >> suspend "failed"
QED

Resume send_tail_path_full[failed]:
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  qexistsl_tac [`step_prov PG G inst u`,`step_taint inst s u tn`,
    `Abort Revert_abort (revert_state
      (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx)))`] >>
  rpt strip_tac >> res_tac >>
  simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def]
QED

Resume send_tail_path_full[normal]:
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  `stmt_state_rel H0 ctx fn cenv cx es1 s` by metis_tac[] >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def,state_rel_def] >>
  `ghost_kept_at lo cenv es1 sm G tn s (step_prov PG G inst u)
     (step_taint inst s u tn)` by
    (drule_all send_call_runtime_frame >> strip_tac >>
     irule callStepPtrTheory.call_ghost_kept_at >> metis_tac[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas` by
    (simp[Abbr `u`,update_var_def] >>
     qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `alloca_history fn (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    suspend "history" >>
  qexistsl_tac [`step_prov PG G inst u`,`step_taint inst s u tn`,
    `OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> state_rel _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==>
    storage_well_formed_on _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `stmt_state_rel H ctx fn cenv cx es1 s` by metis_tac[] >>
  conj_tac >- simp[] >>
  qexists_tac `u with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  simp[] >> rpt conj_tac
  >- (simp[Abbr `u`] >> irule send_tail_none_post >> simp[] >>
      conj_tac >- (qexists_tac `sm` >> simp[]) >>
      qexistsl_tac [`es1`,`s`] >> simp[])
  >- (`ghost_inv_at (DF H) lo d cenv cx es' (step_prov PG G inst u)
         (step_taint inst s u tn) u` by
        (irule send_call_ghost_inv_at >> simp[] >>
         fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      simp[ghostPcTransportPtrTheory.ghost_inv_at_inst_idx])
QED

Resume send_tail_path_full[history]:
  qmatch_asmsub_abbrev_tac `eval_operand (Var out) u = SOME 1w` >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history fn (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qspecl_then [`fn`,`s`,`bb`,`inst`,`u`] mp_tac alloca_history_base_step >>
     simp[is_terminator_def]) >>
  `alloca_inv (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `eval_operand (Var out) (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME 1w` by
    fs[eval_operand_def,lookup_var_def] >>
  `step_inst_base (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] [])
     (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
  qspecl_then [`fn`,`u with vs_inst_idx := SUC s.vs_inst_idx`,`bb`,
    `mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac alloca_history_base_step >>
  simp[mk_inst_def,is_terminator_def]
QED

Finalise send_tail_path_full[local]

Theorem send_tail_outcome_full:
  expr_has_effect e /\
  emit_op CALL [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (success,s3) /\
  emit_void ASSERT [success] s3 = (void,sb) /\ fn_has_code sm sb fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es1 s /\
    storage_well_formed_on cx es1 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es1 G tn s) /\
  wb_frame cenv es es1 sa s0 s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\ es1.gas_obs = [] ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs); read_result cx tv od)
    (es1,s,G,tn)
    (\H res ee G' tn' z. res = INL NoneV /\
      expr_post H ctx fn cenv cx e es sa sb s0 ee NoneV (Lit 0w) z /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' z /\
      ghost_kept_at lo cenv es1 sm G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn z /\ z.vs_alloca_next = s.vs_alloca_next)
    (\H res ee gt r. exprSimDefs$expr_exit res r)
Proof
  strip_tac >>
  qabbrev_tac `src = do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
                       read_result cx tv od` >>
  Cases_on `src es1` >> rename1 `src es1 = (res,ee)` >>
  `ee.gas_obs = es1.gas_obs /\
   !gs. src (es1 with gas_obs := gs) = (res,ee with gas_obs := gs)` by
    (fs[Abbr `src`,SF ETA_ss] >>
     qspec_then `read_result cx` mp_tac (GEN_ALL send_bind_gas_frame) >>
     simp[vyperStateTheory.read_result_def,vyperStateTheory.return_def,SF ETA_ss] >>
     disch_then drule >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `(do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
       read_result cx tv od) es1 = (res,ee)` by fs[Abbr `src`] >>
  reverse (Cases_on `storage_trace_domain cx st0 ee.storage_trace`)
  >- (irule gas_outcome_full_bad_nil >> fs[Abbr `src`]) >>
  `storage_trace_frame src` by
    (simp[Abbr `src`] >>
     irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.storage_trace_frame_send,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es1 s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es1 G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es1.storage_trace` by
       metis_tac[vyperStorageFootprintTheory.valid_horizon_frame] >>
     qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     drule eval_send_read >> strip_tac >>
     irule vyperFiniteStoragePreservationTheory.eval_send_preserves_storage_well_formed_on >>
     conj_tac >- fs[vyperStorageFootprintTheory.valid_horizon_def] >>
     qexistsl_tac [`has_gas`,`r`,`es1`,`to_v::amount_v::gas_vs`] >> simp[]) >>
  drule_all send_tail_path_full >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`,`ee`,`[]`,`r`,`res`,`tn'`] >>
  simp[gasSummaryTheory.gas_explicit_def] >>
  rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED
