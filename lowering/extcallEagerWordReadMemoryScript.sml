(* The actual word snapshot executes the immediate source read. *)
Theory extcallEagerWordReadMemory
Ancestors
  extcallEagerCaptureFrameMemory bodyMemAggregateContinuation
  exprSimMemDefs exprSimUnwrapProps exprSimUnwrap exprSimProps stmtReasonVvMemory
  exprLoweringProps exprLowering loweringPosts compileEnv context
  vyperInterpreter vyperState fragGasMode fragGasPath gasSummary

Theorem extcall_word_eager_read_mem:
  compile_snapshot_vv ce F (ext_call_arg_value (expr_type e) vv) sm =
    (saved,sb) /\
  is_word_type (expr_type e) /\ post_value_type ce e = expr_type e /\
  local_ptrs_reserved ce sm /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v z tag op. saved = StackValue tag op /\
    gas_marked_exec T (ctx,func) (read_result cx raw)
      (ee,s) [] (INL v) ee (OK z) /\
    expr_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op z /\
    vv_holds ce cx (expr_type e) (Value v) saved ee z /\
    vv_at ce cx (expr_type e) sa sb ee (Value v) saved z /\
    vv_store_bound cx (expr_type e) (expr_type e) ee (Value v) saved z /\
    vv_storage_live cx saved ee z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next
Proof
  strip_tac >> drule vv_post_read_ok >> strip_tac >>
  drule_all vv_post_read_result >> strip_tac >>
  `vv_holds ce cx (expr_type e) (Value v) vv ee s` by gvs[vv_post_def] >>
  drule_all eager_word_snapshot_unwrap >> strip_tac >>
  mp_tac (Q.INST [`su` |-> `sb`, `tvv` |-> `raw`, `r` |-> `s`, `es'` |-> `ee`]
    (SPEC_ALL aggregate_rebased_marked_read_mem_capacity)) >>
  (impl_tac >- (pure_asm_rewrite_tac [] >> simp[])) >>
  strip_tac >>
  rename1 `gas_marked_exec T (ctx,func) (read_result cx raw)
    (ee,s) [] (INL resultv) ee (OK outstate)` >>
  `~outstate.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT2 o REWRITE_RULE[gas_marked_exec_def]) >>
     metis_tac[gas_marked_path_exec,gas_path_normal]) >>
  `vv_holds ce cx (expr_type e) (Value resultv) saved ee outstate` by
    gvs[expr_post_def,vv_holds_def,read_result_def,return_def] >>
  `vv_at ce cx (expr_type e) sa sb ee (Value resultv) saved outstate` by
    gvs[vv_at_def,expr_val_at_def,read_result_def,return_def] >>
  qexistsl_tac [`resultv`,`outstate`,`tag`,`op`] >>
  simp[vv_store_bound_stack_word,vv_storage_live_def]
QED
