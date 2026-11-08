(* Sequential memory simulations for RawLog. *)
Theory bodyMemRawLogFragments
Ancestors
  bodyMemRawLogCompose bodyMemRawLogPrepare bodyMemRawLogTopics bodyDeclMemoryCompose bodyMemRawLogAllocation
  bodySimCallRawLog bodySimRawLogBodySource bodySimRawLogSource bodySimRawLogTails
  bodyMemRawLogStages exprSimMemDefs loweringPosts exprSimHyps exprSimAggregateLoops
  exprSimPrecompiles exprSimWordArgs exprSimSource fragGasPath gasSummary fragGasMode gasOutcome
  exprLowering exprLoweringProps freshWrites compileEnv bodyMemoryPreds
  venomState venomInst vyperState vyperValue vyperAST list loweringStateRelDefs

Theorem raw_log_dynamic_data_endpoint_mem[local]:
  expr_body_pre cenv cx env data (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv call = expr_type call /\ expr_type call = NoneT /\
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

Theorem raw_log_fixed_data_endpoint_mem[local]:
  expr_body_pre cenv cx env data (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv call = expr_type call /\ expr_type call = NoneT /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0) marks (INL vs) mid (OK t0) /\
  wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx data) (read_result cx))
    (mid with gas_obs := [],t) marks' (INL v) mid' (OK u) /\
  expr_post ctx func cenv cx data (mid with gas_obs := []) sk sn t
    (mid' with gas_obs := []) v data_op u /\
  emit_void MSTORE [Var pvar;data_op] sn = ((),sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var pvar]) [] sp = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
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
  gas_outcome T tops (ctx,func)
    (do bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bs); return NoneV od)
    (mid' with gas_obs := [],u)
    (\rr ee u. ?v. rr = INL v /\
      expr_post ctx func cenv cx call es sa sb s0 ee v (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next) R
Proof
  strip_tac >> drule_all raw_log_fixed_data_view_mem >> strip_tac >>
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
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by fs[wb_args_post_def] >>
  drule_all raw_log_fixed_buffer_after_data >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) u` by fs[expr_post_def] >>
  `~u.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  irule aggregate_tuple_gas_outcome_mono >>
  irule_at Any raw_log_fixed_continuation_mem >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  qpat_assum `wb_frame _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_type call = NoneT` (irule_at Any) >>
  qpat_assum `MEM inst _` (irule_at Any) >>
  `w2n p + 32 <= u.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`w`, `p`, `R`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!n b sz. local_region _ _ u _ _ _ ==> _` mp_tac >> simp[]
QED

Theorem raw_log_fixed_allocated_mem[local]:
  expr_sim_mem ctx func cenv cx (expr_type data) data (mid with gas_obs := []) /\
  (!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s) /\
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv call = expr_type call /\ expr_type call = NoneT /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0) marks (INL vs) mid (OK t0) /\
  wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t /\
  compile_alloc_buffer 32 sm = (buf,sk) /\ buf.buf_operand = Var pvar /\
  lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn) /\
  emit_void MSTORE [buf.buf_operand;data_op] sn = ((),sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] sp = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
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
  gas_outcome T (cx_tops cx) (ctx,func)
    (do v <- bind (eval_expr cx data) (read_result cx);
        bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bs); return NoneV od)
    (mid with gas_obs := [],t)
    (\rr ee u. ?v. rr = INL v /\
      expr_post ctx func cenv cx call es sa sb s0 ee v (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\rr ee r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by metis_tac[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by fs[wb_args_post_def] >>
  disch_then drule_all >>
  disch_then (mp_then Any irule raw_log_outcome_bind_value) >>
  reverse conj_tac >- (Cases >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee t'. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `rr = INL v` SUBST_ALL_TAC >> qexists_tac `v` >>
  conj_tac >- simp[] >> BETA_TAC >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by
    (first_x_assum irule >> simp[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops` by
    first_assum ACCEPT_TAC >>
  qpat_assum `buf.buf_operand = Var pvar`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  irule raw_log_fixed_data_endpoint_mem >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` (irule_at Any) >>
  qpat_assum `MEM _ (fn_insts _)` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ data (_ with gas_obs := [])` (irule_at Any) >>
  qexists_tac `p` >>
  `s0.vs_alloca_next <= t'.vs_alloca_next /\ sa.cs_next_id <= sk.cs_next_id` by decide_tac >>
  fs[eval_operand_def] >> simp[mk_inst_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
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
  drule_all raw_log_fixed_compile_stages >> strip_tac >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  drule_all raw_log_fixed_stage_structure >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all raw_log_body_topics_sim_mem >>
  disch_then (mp_then Any irule raw_log_outcome_bind_values) >>
  reverse conj_tac >- (Cases >> simp[wb_args_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all raw_log_topics_marked_post_mem >> strip_tac >>
  drule_all raw_log_marked_data_ready_mem >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
   wb_frame cenv es sa s0 t` by fs[wb_args_post_def] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all raw_log_alloc_mem_counted >> strip_tac >>
  `wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t'` by
    (irule raw_log_alloc_args_post >> simp[] >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `t'` >> simp[] >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at sk z) /\ (!l. op <> Label l)) ops` by
    (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  `LENGTH vs = LENGTH topics` by fs[typed_args_post_def] >>
  `LENGTH ops <= 4 /\ LENGTH vs <= 4 /\
   sa.cs_next_var <= sk.cs_next_var /\ s0.vs_alloca_next <= t'.vs_alloca_next` by decide_tac >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  simp[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] raw_log_fixed_allocated_mem) >>
  qpat_assum `expr_sim_mem _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`p`, `w`, `env`] >> fs[expr_type_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
