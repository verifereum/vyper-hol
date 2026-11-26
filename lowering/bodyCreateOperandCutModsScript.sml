(* A reached Create operand and its continuation share one source replay
   and one machine landing, including the linked immutable frame. *)
Theory bodyCreateOperandCutMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach
  bodyBopBytestringBindMods bodyForcedStorageFrameMods
  gasOutcomeFullMods gasOutcomeFullPostMods gasOutcomeFullBindMods gasExemptCertMods haltExitProj
  fragGasOriginPtrExec fragExec exprSimSource vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperStorageFootprint loweringPosts exprSimDefs stmtSimProps
  exprLoweringProps bodyMemoryDefs exprSimHypsDefs vyperState
  bodyWriteSubscriptSourceMods
  gasContext vyperTypeEvalSoundness vyperExprNoControl
Libs
  monadsyntax

val replay = ``!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
  ((res:'a + exception),ee with gas_obs := tail)``;
val path = ``!H. valid_horizon cx st0 H ee.storage_trace ==>
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)``;
val packet = ``?marks. ^replay /\ ^path``;

(* Enrich only the normal post. Choose the marks before quantifying over
   horizons, so the continuation gets the very path that generated replay. *)
Theorem create_operand_post_replay[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) P R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) (\H res ee G1 tn1 t. P H res ee G1 tn1 t /\ ee.gas_obs = [] /\ ^packet) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qmatch_asmsub_rename_tac `gas_origin_ptr_path _ _ marks (r,G1,tn1)` >>
      qexistsl_tac [`res`,`ee`,`r`,`G1`,`tn1`] >> simp[] >>
      qx_gen_tac `H` >> disch_tac >>
      first_assum (drule_then strip_assume_tac) >> simp[] >>
      disj1_tac >> qexists_tac `marks` >> simp[] >>
      rpt strip_tac >> first_assum (drule_then (assume_tac o CONJUNCT1)) >> fs[]) >>
  disj2_tac >> disj2_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem create_operand_value_bind[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (source:evaluation_state -> value evaluation_result)
    (es,s,G,tn) (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee G1 tn1 t) /\
    (?marks. (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                           (INL v,ee with gas_obs := tail)) /\ ^path) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (next v) (ee,t,G1,tn1) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind source next) (es,s,G,tn) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule create_operand_post_replay >> BETA_TAC >> strip_tac >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame source`] >- first_assum ACCEPT_TAC
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  first_assum (irule_at Any) >> BETA_TAC >>
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  first_x_assum irule >> simp[] >> reverse conj_tac
  >- (qmatch_asmsub_rename_tac `gas_origin_ptr_path _ _ chosen (OK t,G1,tn1)` >>
      qexists_tac `chosen` >> simp[]) >>
  rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> gvs[]
QED

val source_expr = ``bind (eval_expr cx e) (read_result cx)``;
val post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sb s ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
  ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
  ghost_kept_at lo cenv es sa G tn s G1 tn1``;
val result_exit = ``\(H:(bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt:(string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val operand_packet = ``?marks.
  (!tail. ^source_expr (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                       (INL v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1))``;

Theorem create_operand_admissible[local]:
  expr_body_pre_mods mods cenv cx env e es ==>
  gas_admissible ^source_expr expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `no_type_error_result res` by
    (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_THM] eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >>
     fs[expr_body_pre_mods_def, expr_sim_inv_mods_def]) >>
  Cases_on `res` >> gvs[expr_res_ok_def] >>
  rename1 `INR exc` >>
  `no_control_exc exc` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  Cases_on `exc` >> gvs[no_control_exc_def,no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem create_body_operand_cut_replay_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sh = (op,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ^post) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\ return_buf_frame d cenv sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    body_const_cells_agree_mods mods cx env ee /\
    expr_sim_inv_mods mods cenv cx env ee /\ expr_result_typed env e (Value v) /\
    (?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\
                        read_result cx tv a' = (INL v',b')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
    ^operand_packet ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next v) (ee,t,G1,tn1) Q ^result_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind ^source_expr next) (es,s,G,tn) Q ^result_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `!DF lo d PG src tops ctx sh fn sfn ce en ty es. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (mp_tac o SRULE [IMP_CONJ_THM,FORALL_AND_THM]) >>
     disch_then (irule o CONJUNCT1) >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`sh`,`shb`,`op`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, drule_then ACCEPT_TAC create_operand_admissible])) >> strip_tac >>
  irule create_operand_value_bind >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H v ee G1 tn1 t. ^post` >> BETA_TAC >>
  reverse conj_tac >- suspend "exit" >> suspend "landing"
QED

Resume create_body_operand_cut_replay_mods[exit]:
  irule gasOutcomeFullPostModsTheory.gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ _ _` (irule_at Any) >>
  BETA_TAC >> conj_tac >- simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                   INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]
QED

Resume create_body_operand_cut_replay_mods[landing]:
  qx_genl_tac [`v`,`ee`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?marks. _ /\ _` (qx_choose_then `marks` strip_assume_tac) >>
  drule_all bop_bytestring_operand_source_mods >>
  disch_then (qspec_then `st0` strip_assume_tac) >>
  `expr_result_typed env e (Value v)` by
    gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def, value_result_typed_def] >>
  `?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\ read_result cx tv a' = (INL v',b')` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_read_INL) >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _` (drule_then assume_tac) >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     fs[expr_post_mods_def, expr_post_def] >>
     qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi_mods >> disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  `!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  qpat_assum `!v ee G1 tn1 t. _ ==> gas_outcome_full_mods _ _ _ _ (next v) _ _ _` irule >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Finalise create_body_operand_cut_replay_mods
