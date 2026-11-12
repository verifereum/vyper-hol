(* Sequential memory simulations for RawLog. *)
Theory bodyMemRawLogFragments
Ancestors
  bodyMemRawLogCompose bodyMemRawLogPrepare bodyMemRawLogTopics bodyDeclMemoryCompose bodyMemRawLogAllocation
  bodySimCallRawLog bodySimRawLogBodySource bodySimRawLogSource bodySimRawLogTails
  bodyMemRawLogStages exprSimMemDefs loweringPosts exprSimHyps exprSimAggregateLoops
  exprSimPrecompiles exprSimWordArgs exprSimSource fragGasPath gasSummary fragGasMode gasOutcome
  exprLowering exprLoweringProps freshWrites compileEnv bodyMemoryPreds
  venomState venomInst vyperState vyperValue vyperAST list loweringStateRelDefs
  gasStorage stmtReasonVvMemory vyperStorageTrace vyperStorageFootprint exprSimRawLog

(* The data endpoint, dynamic payload: the data evaluation ends at one state
   (the horizon-free endpoint) whose posts hold at every valid horizon. *)
Theorem raw_log_dynamic_data_endpoint_mem[local]:
  expr_has_effect call /\
  expr_body_pre cenv cx env data (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv call = expr_type call /\ expr_type call = NoneT /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0) marks (INL vs) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx data) (read_result cx))
    (mid with gas_obs := [],t) marks' (INL v) mid' (OK t') /\
  storage_trace_domain cx st0 mid'.storage_trace /\
  (!H. valid_horizon cx st0 H mid'.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
       (mid' with gas_obs := []) v data_op t') /\
  expr_store_bound cx (expr_type data) v data_op t' /\
  emit_op MLOAD [data_op] sn = (len_op,sl) /\
  emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] sp = ((),sb) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sn /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l)) ops /\
  (!z. data_op = Var z ==> not_fresh_at sn z) /\ LENGTH ops <= 4 /\ LENGTH vs <= 4 /\
  alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
  t'.vs_current_bb = sn.cs_current_bb /\ t'.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (do bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bs); return NoneV od)
    (mid' with gas_obs := [],t')
    (\H rr ee u. ?v. rr = INL v /\
      expr_post H ctx func cenv cx call es sa sb s0 ee v (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\H rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  `?H2. valid_horizon cx st0 H2 mid'.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `bind (eval_expr cx data) (read_result cx)
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL v, mid' with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H2 mid.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx data) (read_result cx))` by
       simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
            storage_trace_frame_read_result] >>
     `valid_horizon cx st0 H2 (mid' with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `eval_exprs cx topics (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H2 es.storage_trace` by
    (`storage_trace_frame (eval_exprs cx topics)` by
       simp[evaluate_storage_trace_frame] >>
     `valid_horizon cx st0 H2 (mid with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `expr_post H2 ctx func cenv cx data (mid with gas_obs := []) sm sn t
     (mid' with gas_obs := []) v data_op t'` by
    (qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `wb_args_post H2 ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> wb_args_post _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `stmt_state_rel H2 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  drule_all raw_log_dynamic_data_bounds_mem >>
  disch_then (qx_choose_then `bs` (qx_choose_then `b`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  drule raw_log_topics_marked_scopes >> strip_tac >>
  drule_all raw_log_data_operands_mem >> strip_tac >>
  `!H. valid_horizon cx st0 H (mid' with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid' with gas_obs := []) t' /\
     storage_well_formed_on cx (mid' with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
     simp[expr_post_def]) >>
  `storage_trace_domain cx st0 (mid' with gas_obs := []).storage_trace` by simp[] >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  drule_all_then assume_tac raw_log_dynamic_continuation_mem >>
  irule aggregate_tuple_gas_outcome_mono >>
  pop_assum (irule_at Any) >>
  conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_log_dynamic_frag_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx args /\
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
     storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\H rr ee t. ?v. rr = INL v /\
      expr_post H ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
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
  gvs[] >>
  drule_all raw_log_mem_source_prepare >> strip_tac >> gvs[] >>
  drule_all raw_log_dynamic_compile_stages >> strip_tac >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  drule_all raw_log_dynamic_stage_structure >> strip_tac >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `expr_has_effect call` by simp[Abbr `call`, loweringPostsTheory.expr_has_effect_thm] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim_mem >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT1 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[wb_args_exit_def]) >>
  (* the topics: one endpoint, the posts at each valid horizon of it *)
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
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
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
     drule_all raw_log_topics_marked_post_mem >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule_all raw_log_topics_marked_post_mem >> simp[]) >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
     simp[typed_args_post_def]) >>
  `LENGTH vs = LENGTH topics` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp[typed_args_post_def]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all raw_log_marked_data_ready_mem >> strip_tac >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by
    (qpat_assum `!s. expr_sim_inv _ _ _ s ==> expr_body_pre _ _ _ data s` irule >>
     first_assum ACCEPT_TAC) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn)` by simp[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule_all >>
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
  qexists_tac `dv` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
       (mid2 with gas_obs := []) dv data_op td /\
     expr_store_bound cx (expr_type data) dv data_op td /\
     td.vs_current_bb = sn.cs_current_bb /\
     td.vs_inst_idx = LENGTH sn.cs_current_insts /\
     alloca_history func td /\ t.vs_alloca_next <= td.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sm sn t
       (mid2 with gas_obs := []) dv data_op td` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `expr_store_bound cx (expr_type data) dv data_op td /\
   td.vs_current_bb = sn.cs_current_bb /\
   td.vs_inst_idx = LENGTH sn.cs_current_insts /\
   alloca_history func td /\ t.vs_alloca_next <= td.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4 /\ s0.vs_alloca_next <= td.vs_alloca_next` by
    decide_tac >>
  `fn_has_code sn sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  qpat_x_assum `Abbrev (call = _)`
    (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  drule_all_then ACCEPT_TAC raw_log_dynamic_data_endpoint_mem
QED

(* The data endpoint, 32-byte payload, after the buffer's ALLOCA. *)
Theorem raw_log_fixed_data_endpoint_mem[local]:
  expr_has_effect call /\
  expr_body_pre cenv cx env data (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv call = expr_type call /\ expr_type call = NoneT /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0) marks (INL vs) mid (OK t0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx data) (read_result cx))
    (mid with gas_obs := [],t) marks' (INL v) mid' (OK u) /\
  storage_trace_domain cx st0 mid'.storage_trace /\
  (!H. valid_horizon cx st0 H mid'.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn t
       (mid' with gas_obs := []) v data_op u) /\
  emit_void MSTORE [Var pvar;data_op] sn = ((),sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var pvar]) [] sp = ((),sb) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sk /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sk.cs_next_var /\ sa.cs_next_id <= sk.cs_next_id /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops /\
  not_fresh_at sk pvar /\ lookup_var pvar t = SOME p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n p,32) /\ sa.cs_next_id <= inst.inst_id /\
  (!n b sz. local_region cenv (mid with gas_obs := []).scopes t n b sz ==>
    regions_disjoint (w2n p) 32 b sz) /\
  LENGTH ops <= 4 /\ LENGTH vs <= 4 /\ alloca_history func u /\
  w2n p + 32 <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (do bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bs); return NoneV od)
    (mid' with gas_obs := [],u)
    (\H rr ee r. ?v. rr = INL v /\
      expr_post H ctx func cenv cx call es sa sb s0 ee v (Lit 0w) r /\
      r.vs_current_bb = sb.cs_current_bb /\ r.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next)
    (\H rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  `?H2. valid_horizon cx st0 H2 mid'.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `bind (eval_expr cx data) (read_result cx)
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL v, mid' with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H2 mid.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx data) (read_result cx))` by
       simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
            storage_trace_frame_read_result] >>
     `valid_horizon cx st0 H2 (mid' with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `eval_exprs cx topics (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H2 es.storage_trace` by
    (`storage_trace_frame (eval_exprs cx topics)` by
       simp[evaluate_storage_trace_frame] >>
     `valid_horizon cx st0 H2 (mid with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `expr_post H2 ctx func cenv cx data (mid with gas_obs := []) sk sn t
     (mid' with gas_obs := []) v data_op u` by
    (qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `wb_args_post H2 ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> wb_args_post _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `stmt_state_rel H2 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  drule_all raw_log_fixed_data_view_mem >> strip_tac >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  drule raw_log_topics_marked_scopes >> strip_tac >>
  drule_all raw_log_data_operands_mem >> strip_tac >>
  `MAP FDOM (mid with gas_obs := []).scopes =
   MAP FDOM (mid' with gas_obs := []).scopes` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_then Any mp_tac
       (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `stmt_state_rel H2 ctx func cenv cx (mid with gas_obs := []) t` by
    fs[wb_args_post_def] >>
  drule_all raw_log_fixed_buffer_after_data >> strip_tac >>
  `!H. valid_horizon cx st0 H (mid' with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid' with gas_obs := []) u /\
     storage_well_formed_on cx (mid' with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
     simp[expr_post_def]) >>
  `storage_trace_domain cx st0 (mid' with gas_obs := []).storage_trace` by simp[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid' with gas_obs := []).scopes` by simp[] >>
  `~u.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `w2n p + 32 <= u.vs_alloca_next` by decide_tac >>
  drule_all_then assume_tac raw_log_fixed_continuation_mem >>
  irule aggregate_tuple_gas_outcome_mono >>
  pop_assum (irule_at Any) >>
  conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* The 32-byte payload after its buffer is allocated: the data. *)
Theorem raw_log_fixed_allocated_mem[local]:
  expr_has_effect call /\
  expr_sim_mem ctx func cenv cx (expr_type data) data (mid with gas_obs := []) /\
  (!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s) /\
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv call = expr_type call /\ expr_type call = NoneT /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0) marks (INL vs) mid (OK t0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t) /\
  compile_alloc_buffer 32 sm = (buf,sk) /\ buf.buf_operand = Var pvar /\
  lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn) /\
  emit_void MSTORE [buf.buf_operand;data_op] sn = ((),sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] sp = ((),sb) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  (!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)) /\
  local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sk /\ fn_has_code sm sk func /\ fn_has_code sk sn func /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sk.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sk.cs_next_id /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops /\
  not_fresh_at sk pvar /\ eval_operand buf.buf_operand t = SOME p /\
  FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n p,32) /\
  (!n b sz. local_region cenv (mid with gas_obs := []).scopes t n b sz ==>
    regions_disjoint (w2n p) 32 b sz) /\
  LENGTH ops <= 4 /\ LENGTH vs <= 4 /\ alloca_history func t /\
  w2n p + 32 <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\ t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (do v <- bind (eval_expr cx data) (read_result cx);
        bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bs); return NoneV od)
    (mid with gas_obs := [],t)
    (\H rr ee r. ?v. rr = INL v /\
      expr_post H ctx func cenv cx call es sa sb s0 ee v (Lit 0w) r /\
      r.vs_current_bb = sb.cs_current_bb /\ r.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next)
    (\H rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by metis_tac[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule_all >>
  disch_then (mp_then Any irule stmtReasonVvMemoryTheory.gas_outcome_bind_value) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT2 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  qx_genl_tac [`marks2`, `res2`, `mid2`, `td`] >> strip_tac >>
  `?H2. valid_horizon cx st0 H2 mid2.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `?dv. res2 = INL dv` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> Cases_on `res2` >> simp[]) >>
  qpat_x_assum `?dv. res2 = INL dv` (qx_choose_then `dv` assume_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  qexists_tac `dv` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn t
       (mid2 with gas_obs := []) dv data_op td /\
     td.vs_current_bb = sn.cs_current_bb /\
     td.vs_inst_idx = LENGTH sn.cs_current_insts /\
     alloca_history func td /\ t.vs_alloca_next <= td.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     expr_post H ctx func cenv cx data (mid with gas_obs := []) sk sn t
       (mid2 with gas_obs := []) dv data_op td` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `td.vs_current_bb = sn.cs_current_bb /\
   td.vs_inst_idx = LENGTH sn.cs_current_insts /\
   alloca_history func td /\ t.vs_alloca_next <= td.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
        expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H2` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `lookup_var pvar t = SOME p` by
    (qpat_x_assum `buf.buf_operand = Var pvar` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     fs[eval_operand_def]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  qpat_assum `buf.buf_operand = Var pvar`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `sa.cs_next_id <= sk.cs_next_id` by decide_tac >>
  `(mk_inst sm.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sm.cs_next_var)]).inst_opcode = ALLOCA /\
   (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sm.cs_next_var)]).inst_id = sm.cs_next_id` by
    simp[mk_inst_def] >>
  `FLOOKUP t.vs_allocas
      (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sm.cs_next_var)]).inst_id = SOME (w2n p,32)` by
    simp[mk_inst_def] >>
  `sa.cs_next_id <= (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sm.cs_next_var)]).inst_id` by simp[mk_inst_def] >>
  drule_all_then ACCEPT_TAC raw_log_fixed_data_endpoint_mem
QED

Theorem raw_log_fixed32_frag_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx args /\
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
     storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\H rr ee t. ?v. rr = INL v /\
      expr_post H ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
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
  gvs[] >>
  drule_all raw_log_mem_source_prepare >> strip_tac >> gvs[] >>
  drule_all raw_log_fixed_compile_stages >> strip_tac >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  drule_all raw_log_fixed_stage_structure >> strip_tac >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `expr_has_effect call` by simp[Abbr `call`, loweringPostsTheory.expr_has_effect_thm] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim_mem >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule (CONJUNCT1 raw_log_tail_trace_frame))
  >~ [`exit_result _`]
  >- (rpt gen_tac >> Cases_on `res` >> simp[wb_args_exit_def]) >>
  (* the topics: one endpoint, the posts at each valid horizon of it *)
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
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
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
     drule_all raw_log_topics_marked_post_mem >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule_all raw_log_topics_marked_post_mem >> simp[]) >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
     simp[typed_args_post_def]) >>
  `LENGTH vs = LENGTH topics` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp[typed_args_post_def]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all raw_log_marked_data_ready_mem >> strip_tac >>
  (* the buffer: one endpoint, its relation at each valid horizon *)
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  `valid_horizon cx st0 H1 (mid with gas_obs := []).storage_trace` by simp[] >>
  `wb_frame cenv es (mid with gas_obs := []) sa s0 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        wb_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t`
       (qspec_then `H1` mp_tac) >> simp[wb_args_post_def]) >>
  drule_all_then (qx_choosel_then [`ta`, `w`] strip_assume_tac)
    raw_log_alloc_mem_counted >>
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
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops` by
    (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  `LENGTH vs = LENGTH topics` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        typed_args_post H ctx func cenv cx es sa s0 (mid with gas_obs := [])
          topics ops vs t /\ _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp[typed_args_post_def]) >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4 /\
   sa.cs_next_var <= sk.cs_next_var /\ s0.vs_alloca_next <= ta.vs_alloca_next` by
    decide_tac >>
  qpat_x_assum `Abbrev (call = _)`
    (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `ta` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then ACCEPT_TAC (SRULE [SF ETA_ss] raw_log_fixed_allocated_mem)
QED
