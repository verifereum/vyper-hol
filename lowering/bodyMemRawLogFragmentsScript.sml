(* Sequential memory simulations for RawLog. *)
Theory bodyMemRawLogFragments
Ancestors
  bodyMemRawLogCompose bodyMemRawLogPrepare bodyMemRawLogTopics
  bodySimCallRawLog bodySimRawLogBodySource bodySimRawLogSource
  bodyMemRawLogStages exprSimMemDefs loweringPosts exprSimHyps exprSimAggregateLoops
  exprSimPrecompiles exprSimWordArgs exprSimSource fragGasPath gasSummary fragGasMode gasOutcome
  exprLowering exprLoweringProps freshWrites compileEnv bodyMemoryPreds
  venomState vyperState vyperValue vyperAST list

Theorem raw_log_dynamic_data_endpoint_mem[local]:
  expr_body_pre cenv cx env data (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\ expr_type call = NoneT /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0) marks (INL vs) mid (OK t) /\
  wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx data) (read_result cx))
    (mid with gas_obs := [],t) marks' (INL v) mid' (OK t') /\
  expr_post ctx func cenv cx data (mid with gas_obs := []) sm sn t
    (mid' with gas_obs := []) v data_op t' /\
  expr_store_bound cx (expr_type data) v data_op t' /\
  emit_op MLOAD [data_op] sn = (len_op,sl) /\
  emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] sp = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sn /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l)) ops /\
  (!z. data_op = Var z ==> not_fresh_at sn z) /\ LENGTH ops <= 4 /\ LENGTH vs <= 4 /\
  alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
  t'.vs_current_bb = sn.cs_current_bb /\ t'.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  gas_outcome T tops (ctx,func)
    (do bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bs); return NoneV od)
    (mid' with gas_obs := [],t')
    (\rr ee u. ?v. rr = INL v /\
      expr_post ctx func cenv cx call es sa sb s0 ee v (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next) R
Proof
  strip_tac >>
  drule_all raw_log_dynamic_data_bounds_mem >>
  disch_then (qx_choose_then `bs` (qx_choose_then `b`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  drule raw_log_topics_marked_scopes >> strip_tac >>
  drule_all raw_log_data_operands_mem >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by fs[expr_post_def] >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  irule aggregate_tuple_gas_outcome_mono >>
  irule_at Any raw_log_dynamic_continuation_mem >>
  qpat_assum `emit_op MLOAD _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  qpat_assum `wb_frame _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_type call = NoneT` (irule_at Any) >>
  qexistsl_tac [`b`, `R`] >> simp[] >> decide_tac
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
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0)
    (\rr ee t. ?v. rr = INL v /\
      expr_post ctx func cenv cx (Call ann RawLog args dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\rr ee r. expr_exit rr r)
Proof
  strip_tac >> gvs[] >>
  drule_all raw_log_mem_source_prepare >> strip_tac >> gvs[] >>
  drule_all raw_log_dynamic_compile_stages >> strip_tac >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  drule_all raw_log_dynamic_stage_structure >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim_mem >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  reverse conj_tac >- (Cases >> simp[wb_args_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all raw_log_topics_marked_post_mem >> strip_tac >>
  drule_all raw_log_marked_data_ready_mem >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    fs[wb_args_post_def] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by metis_tac[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn)` by simp[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule_all >>
  disch_then (mp_then Any irule raw_log_outcome_bind_value) >>
  reverse conj_tac >- (Cases >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by
    (first_x_assum irule >> simp[]) >>
  `expr_store_bound cx (expr_type data) v data_op t'` by simp[] >>
  `LENGTH vs = LENGTH topics` by fs[typed_args_post_def] >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4 /\
   s0.vs_alloca_next <= t'.vs_alloca_next` by decide_tac >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  irule raw_log_dynamic_data_endpoint_mem >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_op MLOAD _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ data (_ with gas_obs := [])` (irule_at Any) >>
  qexists_tac `ops` >> simp[expr_type_def, APPEND]
QED
