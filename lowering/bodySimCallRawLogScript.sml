(* Piece of bodySimCallCases.body_raw_log_case. *)

Theory bodySimCallRawLog
Ancestors
  bodySimExprCases bodySimRawLog bodySimRawLogTopics gasOutcome gasSummaryCompose gasExemptCert
  bodySimRawLogBodySource bodySimRawLogTails bodySimRawLogSource
  gasSummary gasStorage stmtReasonVvMemory fragGasMode fragGasPath stmtSimDeclCompose
  vyperStorageTrace vyperStorageFootprint
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph
  exprSimSend vyperTypeSystem exprSimAggregateSource vyperValue
  exprSimWordArgs exprLowering compileEnv loweringStateRelDefs emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource vyperEvent
  fragExec venomInst exprSimHash exprSimBuffer exprSimPrecompiles emitHelperProps
  ASCIInumbers exprSimRawLog
Libs
  pairLib

(* The value-list instance of gas_outcome_bind_value (stmtReasonVvMemory):
   the exempt-certificate constructors are typed per result type. *)
Theorem raw_log_outcome_bind_values:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> (value list) evaluation_result) (es,s0) Qa Ra /\
  (!marks res mid t.
     gas_marked_exec memory (ctx,func) a (es,s0) marks res mid (OK t) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Qa H res (mid with gas_obs := []) t) ==>
     ?v. res = INL v /\
         gas_outcome memory tops (ctx,func) cx st0 (k v)
           (mid with gas_obs := [], t) Q R) /\
  (!H res ee r. exit_result r /\ Ra H res ee r ==>
     ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (qexists_tac `left` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[])
  >- (rpt BasicProvers.VAR_EQ_TAC >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (qexists_tac `left` >> disj1_tac >>
          irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[] >>
          irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      qpat_x_assum `!m r e t. gas_marked_exec _ _ _ _ _ _ _ _ /\ _ ==> _`
        (qspecl_then [`left`, `res`, `es_end`, `t`] mp_tac) >>
      impl_tac >- fs[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `gas_outcome _ _ _ _ _ (k _) _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def] >>
      disch_then (qx_choose_then `right` strip_assume_tac)
      >- (qexists_tac `left ++ right` >> disj1_tac >>
          irule gasStorageTheory.gas_bad_storage_at_bind_right >>
          metis_tac[])
      >- (qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
          qpat_x_assum `gas_summary_at _ _ _ (k _) _ _ _`
            (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
          rename1 `gas_marked_exec _ _ (k v) _ right rr fin rq` >>
          qexistsl_tac [`rr`, `fin`, `rq`] >>
          (conj_tac
           >- (irule gas_marked_exec_bind_normal >>
               qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
           simp[])) >>
      qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
      rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
      qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
      simp[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_values >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[GSYM ignore_bind_def])
  >- (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (qexists_tac `left` >> disj1_tac >>
          irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[] >>
          irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
        metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `?ex. res = INR ex` by metis_tac[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qexists_tac `left` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_x_assum `!H res ee r. exit_result _ /\ _ ==> _`
        (qspecl_then [`H`, `INR ex`, `es_end with gas_obs := []`, `r`] mp_tac) >>
      simp[]) >>
  qexists_tac `left` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_values >> simp[GSYM ignore_bind_def]
QED

Theorem expr_body_pre_make_array_arg:
  expr_body_pre cenv cx env (Builtin ann (MakeArray t b) args) es /\
  MEM e args /\ expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env e es'
Proof
  strip_tac >> drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]
QED

Theorem raw_log_dynamic_frag:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data cap.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Dynamic cap))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx))
    expr_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\H rr ee t. ?v. rr = INL v /\
      expr_post H ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ok cx topics` by
    (qpat_assum `body_exprs_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ok_def]) >>
     drule_all body_make_array_children_ok >> simp[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_make_array_arg, MEM]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `lower_value compile_expr cenv _ data sm = (data_op,sn)` >>
  rename1 `emit_op MLOAD [data_op] sn = (len_op,sl)` >>
  rename1 `emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp)` >>
  rename1 `emit_inst LOG _ [] sp = ((),sb)` >>
  `!s. expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  qpat_x_assum `well_typed_expr env (Builtin _ _ _)` kall_tac >>
  qpat_x_assum `well_typed_expr env data` kall_tac >>
  qpat_x_assum `EVERY _ (MAP expr_type topics)` kall_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sn sl /\ cs_extends sl sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sb /\ cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. data_op = Var z ==> not_fresh_at sn z` by
    (drule exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `expr_has_effect call` by simp[Abbr `call`, loweringPostsTheory.expr_has_effect_thm] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT1 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[wb_args_exit_def]) >>
  (* the topics: one endpoint, the post at each valid horizon of it *)
  qx_genl_tac [`marks`, `res`, `mid`, `t`] >> strip_tac >>
  `?H1. valid_horizon cx st0 H1 mid.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `?vs. res = INL vs` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> Cases_on `res` >> simp[]) >>
  qpat_x_assum `?vs. res = INL vs` (qx_choose_then `vs` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  qexists_tac `vs` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
       topics ops vs t /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule_all raw_log_topics_marked_post >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule_all raw_log_topics_marked_post >> simp[]) >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ _ _` mp_tac >> simp[]) >>
     simp[typed_args_post_def]) >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `storage_trace_frame (eval_exprs cx topics)` by
    simp[evaluate_storage_trace_frame] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (mid with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >>
     simp[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  drule_all raw_log_marked_data_ready >> strip_tac >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by
    (qpat_assum `!s. expr_sim_inv _ _ _ s ==> expr_body_pre _ _ _ data s` irule >>
     first_assum ACCEPT_TAC) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn)` by simp[] >>
  drule_all expr_sim_apply >>
  disch_then (mp_then Any irule stmtReasonVvMemoryTheory.gas_outcome_bind_value) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT2 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  (* the data: again one endpoint with the post at each valid horizon *)
  qx_genl_tac [`marks2`, `res2`, `mid2`, `td`] >> strip_tac >>
  `?H2. valid_horizon cx st0 H2 mid2.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `?dv. res2 = INL dv` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> Cases_on `res2` >> simp[]) >>
  qpat_x_assum `?dv. res2 = INL dv` (qx_choose_then `dv` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
       (mid2 with gas_obs := []) dv data_op td /\
     td.vs_current_bb = sn.cs_current_bb /\
     td.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `td.vs_current_bb = sn.cs_current_bb /\ td.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
          (mid2 with gas_obs := []) dv data_op td /\ _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `bind (eval_expr cx data) (read_result cx)
     (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings) =
     (INL dv, mid2 with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx data) (read_result cx))` by
    simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `valid_horizon cx st0 H2 mid.storage_trace` by
    (`valid_horizon cx st0 H2 (mid2 with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `valid_horizon cx st0 H2 es.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        valid_horizon _ _ H es.storage_trace` (qspec_then `H2` mp_tac) >> simp[]) >>
  `wb_args_post H2 ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `stmt_state_rel H2 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `expr_post H2 ctx func cenv cx data (mid with gas_obs := []) sm sn t
     (mid2 with gas_obs := []) dv data_op td` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
          (mid2 with gas_obs := []) dv data_op td /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env data
    (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings)` by simp[] >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. dv = BytesV bs` by
    (qpat_x_assum `!v'. INL dv = _ ==> _` mp_tac >>
     simp[] >> Cases_on `dv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `?bs. dv = BytesV bs` (qx_choose_then `bs` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  qexists_tac `BytesV bs` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  drule_all raw_log_data_post_transport >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by
    (`expr_body_pre cenv cx env data mid` by simp[] >>
     drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  drule_all raw_log_dynamic_data_view >> strip_tac >>
  `!H. valid_horizon cx st0 H (mid2 with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid2 with gas_obs := []) td /\
     storage_well_formed_on cx (mid2 with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
          (mid2 with gas_obs := []) (BytesV bs) data_op td /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ _ _` mp_tac >> simp[]) >>
     simp[expr_post_def]) >>
  `valid_horizon cx st0 H2 (mid2 with gas_obs := []).storage_trace` by simp[] >>
  `~td.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >>
     simp[] >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `LENGTH vs = LENGTH topics` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _` (qspec_then `H2` mp_tac) >>
     simp[typed_args_post_def]) >>
  `eval_operands ops td = SOME (MAP event_value_to_word vs)` by
    (qpat_x_assum `LIST_REL _ ops vs` mp_tac >>
     rpt (pop_assum kall_tac) >> qid_spec_tac `vs` >>
     Induct_on `ops` >> Cases_on `vs` >>
     simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (fs[EVERY_MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4 /\ sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `fn_has_code sn sb func` by metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  qpat_x_assum `Abbrev (call = _)`
    (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  drule_all_then (qx_choose_then `tl` strip_assume_tac)
    raw_log_dynamic_tail_counted >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  irule raw_log_tail_summary >> qexists_tac `tl` >>
  conj_tac >- simp[dest_BytesV_def] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  BETA_TAC >> gen_tac >> strip_tac >>
  qexists_tac `NoneV` >> conj_tac >- REFL_TAC >>
  conj_tac
  >- (irule raw_log_post_gas_obs >>
      qpat_assum `!H. valid_horizon _ _ H (mid2 with gas_obs := []).storage_trace ==>
          expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` irule >>
      asm_simp_tac (srw_ss()) []) >>
  simp[]
QED

Theorem raw_log_alloc_args_post:
  wb_args_post H ctx func cenv cx es0 sa s0 es ops vals t /\
  stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sa s0 u /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
              (!l. op <> Label l)) ops /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) ==>
  wb_args_post H ctx func cenv cx es0 sa s0 es ops vals u
Proof
  simp[wb_args_post_def] >> strip_tac >> simp[] >>
  qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
  qpat_x_assum `EVERY _ ops` mp_tac >>
  qid_spec_tac `vals` >> Induct_on `ops` >> simp[] >>
  gen_tac >> Cases_on `vals` >> simp[] >> rpt strip_tac
  >- (Cases_on `h` >> gvs[eval_operand_def] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem raw_log_fixed32_body_frag:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Fixed 32))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx))
    expr_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\H rr ee t. ?v. rr = INL v /\
      expr_post H ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ok cx topics` by
    (qpat_assum `body_exprs_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ok_def]) >>
     drule_all body_make_array_children_ok >> simp[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_make_array_arg, MEM]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  `!s. expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `compile_alloc_buffer 32 sm = (buf,sk)` >>
  rename1 `lower_value compile_expr cenv _ data sk = (data_op,sn)` >>
  rename1 `emit_void MSTORE _ sn = (u,sp)` >>
  rename1 `emit_inst LOG _ [] sp = (u,sb)` >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  qpat_x_assum `well_typed_expr env (Builtin _ _ _)` kall_tac >>
  qpat_x_assum `well_typed_expr env data` kall_tac >>
  qpat_x_assum `EVERY _ (MAP expr_type topics)` kall_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sk /\ sm.cs_next_var <= sk.cs_next_var /\
   sm.cs_next_id <= sk.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_inst_def,
         comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sk sn /\ sk.cs_next_var <= sn.cs_next_var /\
   sk.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
          fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sb /\ cs_extends sk sb /\ cs_extends sn sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sk func /\ fn_has_code sk sn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sk /\
   local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `expr_has_effect call` by simp[Abbr `call`, loweringPostsTheory.expr_has_effect_thm] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT1 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[wb_args_exit_def]) >>
  (* the topics *)
  qx_genl_tac [`marks`, `res`, `mid`, `t`] >> strip_tac >>
  `?H1. valid_horizon cx st0 H1 mid.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `?vs. res = INL vs` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> Cases_on `res` >> simp[]) >>
  qpat_x_assum `?vs. res = INL vs` (qx_choose_then `vs` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  qexists_tac `vs` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
       topics ops vs t /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule_all raw_log_topics_marked_post >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule_all raw_log_topics_marked_post >> simp[]) >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ _ _` mp_tac >> simp[]) >>
     simp[typed_args_post_def]) >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `storage_trace_frame (eval_exprs cx topics)` by
    simp[evaluate_storage_trace_frame] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (mid with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >>
     simp[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  drule_all raw_log_marked_data_ready >> strip_tac >>
  (* the buffer: one endpoint, its relation at each valid horizon *)
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  `valid_horizon cx st0 H1 (mid with gas_obs := []).storage_trace` by simp[] >>
  `wb_frame cenv es (mid with gas_obs := []) sa s0 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t`
       (qspec_then `H1` mp_tac) >> simp[wb_args_post_def]) >>
  drule_all_then (qx_choosel_then [`ta`, `w`] strip_assume_tac)
    raw_log_alloc_counted >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs ta` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (mid with gas_obs := []).storage_trace` by simp[] >>
     `stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) ta` by
       (qpat_assum `!H. valid_horizon _ _ H (mid with gas_obs := []).storage_trace ==>
           stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) ta`
          (qspec_then `H` mp_tac) >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     irule raw_log_alloc_args_post >> simp[] >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) ta /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H (mid with gas_obs := []).storage_trace ==>
           stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) ta`
          (qspec_then `H` mp_tac) >> simp[])
     >- (qpat_assum `!H. valid_horizon _ _ H (mid with gas_obs := []).storage_trace ==>
           stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\ _`
          (qspec_then `H` mp_tac) >> simp[])) >>
  irule gas_outcome_zero_prefix >> qexists_tac `ta` >> simp[] >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by
    (qpat_assum `!s. expr_sim_inv _ _ _ s ==> expr_body_pre _ _ _ data s` irule >>
     first_assum ACCEPT_TAC) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn)` by simp[] >>
  drule_all expr_sim_apply >>
  disch_then (mp_then Any irule stmtReasonVvMemoryTheory.gas_outcome_bind_value) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT2 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  (* the data *)
  qx_genl_tac [`marks2`, `res2`, `mid2`, `td`] >> strip_tac >>
  `?H2. valid_horizon cx st0 H2 mid2.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `?dv. res2 = INL dv` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> Cases_on `res2` >> simp[]) >>
  qpat_x_assum `?dv. res2 = INL dv` (qx_choose_then `dv` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn ta
       (mid2 with gas_obs := []) dv data_op td /\
     td.vs_current_bb = sn.cs_current_bb /\
     td.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `td.vs_current_bb = sn.cs_current_bb /\ td.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn ta
          (mid2 with gas_obs := []) dv data_op td /\ _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `bind (eval_expr cx data) (read_result cx)
     (mid with gas_obs := gas_explicit marks2 ta.vs_gas_readings) =
     (INL dv, mid2 with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx data) (read_result cx))` by
    simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `valid_horizon cx st0 H2 mid.storage_trace` by
    (`valid_horizon cx st0 H2 (mid2 with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `valid_horizon cx st0 H2 (mid with gas_obs := []).storage_trace` by simp[] >>
  `valid_horizon cx st0 H2 es.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        valid_horizon _ _ H es.storage_trace` (qspec_then `H2` mp_tac) >> simp[]) >>
  `wb_args_post H2 ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs ta` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs ta`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `stmt_state_rel H2 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `stmt_state_rel H2 ctx func cenv cx (mid with gas_obs := []) ta` by
    (qpat_assum `!H. valid_horizon _ _ H (mid with gas_obs := []).storage_trace ==>
        stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) ta /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `expr_post H2 ctx func cenv cx data (mid with gas_obs := []) sk sn ta
     (mid2 with gas_obs := []) dv data_op td` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn ta
          (mid2 with gas_obs := []) dv data_op td /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env data
    (mid with gas_obs := gas_explicit marks2 ta.vs_gas_readings)` by simp[] >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. dv = BytesV bs` by
    (qpat_x_assum `!v'. INL dv = _ ==> _` mp_tac >>
     simp[] >> Cases_on `dv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `?bs. dv = BytesV bs` (qx_choose_then `bs` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  qexists_tac `BytesV bs` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  `sa.cs_next_var <= sk.cs_next_var /\ sa.cs_next_id <= sk.cs_next_id` by decide_tac >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops` by
    (fs[EVERY_MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all raw_log_data_post_transport >> strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM mid2.scopes` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     disch_then (mp_then Any mp_tac
       (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `lookup_var p ta = SOME w` by fs[eval_operand_def] >>
  `MAP FDOM (mid with gas_obs := []).scopes =
   MAP FDOM (mid2 with gas_obs := []).scopes` by simp[] >>
  `sa.cs_next_id <= sm.cs_next_id` by simp[] >>
  drule_all raw_log_fixed_buffer_after_data >> strip_tac >>
  `!H. valid_horizon cx st0 H (mid2 with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid2 with gas_obs := []) td /\
     storage_well_formed_on cx (mid2 with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn ta
          (mid2 with gas_obs := []) (BytesV bs) data_op td /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ _ _` mp_tac >> simp[]) >>
     simp[expr_post_def]) >>
  `valid_horizon cx st0 H2 (mid2 with gas_obs := []).storage_trace` by simp[] >>
  `~td.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >>
     simp[] >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `LENGTH vs = LENGTH topics` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _` (qspec_then `H2` mp_tac) >>
     simp[typed_args_post_def]) >>
  `eval_operands ops td = SOME (MAP event_value_to_word vs)` by
    (qpat_x_assum `LIST_REL _ ops vs` mp_tac >>
     rpt (pop_assum kall_tac) >> qid_spec_tac `vs` >>
     Induct_on `ops` >> Cases_on `vs` >>
     simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4` by decide_tac >>
  `fn_has_code sn sb func` by metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `LENGTH bs = 32` by fs[vyperTypingTheory.value_has_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Fixed 32)))` by simp[vyperValueTheory.evaluate_type_def] >>
  `eval_operand data_op td = SOME
     (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs))` by
    (`post_value_type cenv data = expr_type data` by
       (irule post_value_type_word >> simp[is_word_type_def]) >>
     qpat_assum `expr_post H2 _ _ _ _ data _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def, expr_val_at_def] >>
     asm_simp_tac std_ss [post_value_type_word, is_word_type_def] >> strip_tac >>
     drule exprBopSimPropsTheory.expr_val_rel_typed >>
     simp[is_word_type_def] >> disch_then irule >> gvs[]) >>
  `TAKE 32 (word_to_bytes_be
     (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs))) = bs` by
    (qpat_assum `LENGTH bs = 32` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     qpat_assum `LENGTH bs = 32`
       (fn th => CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM th))))) >>
     irule typed_bytes_prefix >> simp[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  `MAP FDOM es.scopes = MAP FDOM (mid2 with gas_obs := []).scopes` by simp[] >>
  ` (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sm.cs_next_var)]).inst_opcode = ALLOCA /\
    (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sm.cs_next_var)]).inst_id = sm.cs_next_id` by simp[mk_inst_def] >>
  `FLOOKUP td.vs_allocas
    (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sm.cs_next_var)]).inst_id = SOME (w2n w,32)` by simp[mk_inst_def] >>
  qpat_x_assum `Abbrev (call = _)`
    (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  drule_all_then (qx_choose_then `tl` strip_assume_tac)
    raw_log_fixed_tail_counted >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  irule raw_log_tail_summary >> qexists_tac `tl` >>
  conj_tac >- simp[dest_BytesV_def] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  BETA_TAC >> gen_tac >> strip_tac >>
  qexists_tac `NoneV` >> conj_tac >- REFL_TAC >>
  conj_tac
  >- (irule raw_log_post_gas_obs >>
      qpat_assum `!H. valid_horizon _ _ H (mid2 with gas_obs := []).storage_trace ==>
          expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` irule >>
      asm_simp_tac (srw_ss()) []) >>
  simp[]
QED

Theorem raw_log_body_expr_ok:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
Proof
  rpt gen_tac >> strip_tac >> match_mp_tac body_expr_ok_intro >> conj_tac >- gvs[] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim ctx func cenv cx ty (Call v20 RawLog es v21) es'` by
    (simp[expr_sim_def] >> rpt strip_tac >>
     drule_all raw_log_body_lower_value >> strip_tac >> gvs[] >>
     drule raw_log_body_pre_shape >> strip_tac >> gvs[]
     >- (irule raw_log_fixed32_body_frag >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
     irule raw_log_dynamic_frag >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule expr_vv_sim_stack >> simp[] >>
  conj_tac >- (drule raw_log_body_compile_stack >> metis_tac[]) >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       lift_option_type_def, type_check_def, check_not_static_def,
       assert_def, raise_def, push_log_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
