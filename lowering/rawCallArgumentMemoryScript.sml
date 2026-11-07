(* Memory-mode argument binding for raw_call. *)
Theory rawCallArgumentMemory
Ancestors
  rawCallSuffixMemory bodyMemRawCallBounds exprSimRawCall exprSimMemDefs
  bodyMemoryPreds gasOutcome exprSimDefs exprSimProps loweringPosts exprLoweringProps
  compileEnv venomState vyperInterpreter vyperState bodyArgsMemory

Theorem raw_call_mem_value_bind:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gs v ee t.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
    ee.gas_obs = [] /\ expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
    gas_outcome T (cx_tops cx) (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >> disch_then drule_all >> strip_tac >>
  irule raw_call_value_outcome_bind >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `rr` >> gvs[expr_exit_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_call_data_prefix_code[local]:
  emit_op MLOAD [ptr_op] sa = (len_op,sl) /\
  emit_op ADD [ptr_op;Lit 32w] sl = (data_op,sm) ==>
  sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sm)
Proof
  simp[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem raw_call_data_prefix_counted_mem:
  emit_op MLOAD [ptr_op] sa = (len_op,sl) /\
  emit_op ADD [ptr_op;Lit 32w] sl = (data_op,sm) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\
  b < dimword (:256) /\ b + 32 <= s.vs_alloca_next /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
    gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sm.cs_current_insts) /\
    t.vs_current_bb = sm.cs_current_bb /\
    eval_operand len_op t = SOME (n2w len) /\
    eval_operand data_op t = SOME (n2w (b + 32)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> drule_all exprSimHashTheory.hash_data_prefix_run >> strip_tac >>
  drule_all raw_call_data_prefix_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule raw_call_data_prefix_mem_ok >> goal_assum (drule_at Any) >>
     simp[wordsTheory.w2n_n2w] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by fs[listTheory.EVERY_MEM] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sm)) = 0` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all bodyMemBiMethodIdSuffixTheory.method_id_run_path_mem >>
  simp[fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem raw_call_kwargs_sim_mem:
  EVERY (\k. k = EKValue \/ k = EKGas) ks /\ LENGTH es = LENGTH ks /\
  typed_args_ready_mem ctx func cenv cx (K (BaseT (UintT 256))) Inv es /\ Inv st /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  wb_args_shape cenv (K (BaseT (UintT 256))) es /\
  compile_ext_call_kwargs compile_expr cenv NoneT ks es sa = ((vo,go,d),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx st s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx es) (st,s0)
    (\rr ee s. ?xs vs. rr = INL vs /\
      typed_args_post ctx func cenv cx st sa s0 ee es xs vs s /\
      vo = ext_call_kwarg EKValue ks xs /\
      go = ext_call_kwarg EKGas ks xs /\ d = NONE /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all raw_call_kwargs_word_args >> strip_tac >>
  drule_all lower_typed_args_sim_mem >> strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexists_tac `xs` >> simp[]
QED
