(* Evaluate the positional head once and pass its successful read to the
   snapshot suffix at the actual child endpoint. *)
Theory bodyExtPosAggregateHeadMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimMemorySource bodyPtrAttributeSource haltExitProj stmtSimProps exprSimDefs
  vyperStorageTrace vyperStorageFootprint loweringPosts bodyPtrDefs exprSimMemDefs
  gasOutcomeFullMods gasOutcome gasContext gasSummary fragExec fragGasOriginPtr
  exprLowering compileEnv venomState vyperInterpreter vyperState words
Libs monadsyntax

Theorem aggregate_raw_read[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s ==>
  ?v. read_result cx tv ee = (INL v,ee)
Proof
  simp[vv_post_mods_def] >> strip_tac >> Cases_on `vv`
  >- fs[vv_holds_mods_def,vv_holds_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
  >- fs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  fs[vv_holds_mods_def] >> drule_then strip_assume_tac attribute_vv_holds_read_operand >> simp[]
QED

val head_entry = ``
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val head_exit = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : value + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val head_raw_post = ``
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d ce cx ee G tn s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn``;

Theorem ext_pos_aggregate_read_bind[local]:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\ ^head_entry /\
  (!marks tv v ee G tn s.
    eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee) /\
    ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\ ~s.vs_halted /\
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ^head_raw_post) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      ce.ce_modules cx st0 (read_result cx tv) (ee,s,G,tn) Q (^head_exit)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q (^head_exit)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn s. childQ H res ee G tn s /\ ee.gas_obs = [] /\ ~s.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume ext_pos_aggregate_read_bind[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  drule_then strip_assume_tac aggregate_raw_read >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  qpat_assum `!marks tv v ee G tn s. eval_expr _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`marks`,`tv`,`v`,`ee`,`G`,`tn`,`s`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [sumTheory.INL_11]) >>
    gvs[])) >>
  disch_then ACCEPT_TAC
QED

Finalise ext_pos_aggregate_read_bind
