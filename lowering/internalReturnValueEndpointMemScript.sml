(* Return-selected physical-layout bounds at expression endpoints. *)
Theory internalReturnValueEndpointMem
Ancestors
  bodyMemoryDefs externalNormalizePremises exprSimProps loweringPosts exprSimMemDefs
  exprSimMemUnwrap bodyRhsRoomMemory stmtReasonVvMemory
  exprLowering emitHelper fragGasPathMem exprSimUnwrap exprSimUnwrapProps
  exprLoweringProps exprOperandVar emitHelperProps loweringSlice
  vyperEvalExprPreservesScopesDom fragGasPath fragExec exprSimDefs
  exprSimSubscriptMap
  vyperState context compileEnv gasOutcome gasSummary fragGasMode exprSimMemorySource list

Theorem internal_return_nonbytes_value_endpoint_mem:
  expr_sim_mem ctx func ce cx ct e es /\
  lower_value compile_expr ce ct e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func ce cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      (!sty stv. post_value_type ce e = sty /\
        evaluate_type (get_tenv cx) sty = SOME stv /\
        value_has_type stv v /\ ~is_bytestring_type sty ==>
        expr_store_bound cx sty v op t /\
        (~is_word_type sty ==>
         ?sw. eval_operand op t = SOME sw /\
           (type_memory_size stv = 0 \/
            w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
           w2n sw + type_memory_size stv < dimword (:256))))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qexists_tac `v` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type (post_value_type ce e)`
  >- simp[expr_store_bound_word] >>
  `stmt_state_rel ctx func ce cx ee t /\
   expr_val_at ce cx (post_value_type ce e) sa sb ee v op t` by fs[expr_post_def] >>
  drule_all normalize_source_window >> strip_tac >>
  reverse conj_tac >- (simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `val_wf stv v` by fs[expr_val_at_def] >>
  simp[expr_store_bound_def] >> rpt strip_tac >> gvs[] >>
  drule val_store_size_le >> strip_tac >> decide_tac
QED
