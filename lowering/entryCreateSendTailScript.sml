(* Scope the selected Send transfer at its actual CALL or ASSERT landing. *)
Theory entryCreateSendTail
Ancestors
  bodyFullSendPost entryCreateSendSuffix entryCreatePendingScope
  entryCreateCompletedCut entryCreateFocusSpec entryCreatePathScope
  gasOutcomeFull gasStorage gasSummary fragGasOriginPtr vyperStorageFootprint
  vyperState exprSimDefs

Theorem send_tail_outcome_scoped:
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
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
               NONE => 0 | SOME g => g) /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\ es1.gas_obs = [] ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,fn,PG) tops cx st0 sm sb
    (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs); read_result cx tv od)
    (es1,s,G,tn)
    (\H res ee G' tn' z. res = INL NoneV /\
      expr_post H ctx fn cenv cx e es sa sb s0 ee NoneV (Lit 0w) z /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' z /\
      ghost_kept_at lo cenv es1 sm G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn z /\ z.vs_alloca_next = s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all send_tail_outcome_selected >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  simp[gas_explicit_def]
  >- (disj1_tac >> simp[gas_bad_storage_at_def,gas_explicit_def] >>
      conj_tac >- (irule create_operand_focus_scope_caller >> qexists_tac `s` >> simp[]) >>
      qexistsl_tac [`storage_trace_horizon es1.storage_trace`,`fn`,`PG`,`G`,`tn`,`s`] >>
      simp[storage_trace_domain_def,gas_origin_ptr_focus_nil]) >>
  disj2_tac >> disj1_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `create_operand_at sm s` by simp[create_operand_at_def] >>
  qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac (assume_tac o CONJUNCT1)) >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  qabbrev_tac `ops = [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w]` >>
  gvs[LET_THM]
  >- (irule create_send_effect_abort_scope >> simp[] >>
      qexistsl_tac [`ops`,`out`,`s3`] >> simp[])
  >- (irule create_send_effect_abort_scope >> simp[] >>
      qexistsl_tac [`ops`,`out`,`s3`] >> simp[] >>
      disj2_tac >> qexists_tac `u` >> simp[]) >>
  drule_all create_send_effect_ok_scope >> simp[]
QED
