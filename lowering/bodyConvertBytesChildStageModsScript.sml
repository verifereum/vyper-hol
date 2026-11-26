(* Force the Convert operand at the paired prefix cut, retaining its buffer capacity. *)
Theory bodyConvertBytesChildStageMods
Ancestors
  bodyConvertOperandBufferMods bodyFullPredsMods bodyFullPostsMods
  exprSimConvert exprSimStack exprSimDefs loweringPosts
  gasShadowState compileEnv fragExec vyperInterpreter vyperState words
Libs monadsyntax

Theorem convert_bytes_child_stage:
  expr_body_pre_mods mods ce cx env e es /\ is_bytestring_type (expr_type e) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
    (gas_shadow_expr e) sha = (op,shm) /\
  gas_shadow_state sa sha /\ gas_shadow_state sm shm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx (TypeBuiltin dst Convert dst [e])) expr_vv_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v pt rt w. res = INL v /\
      expr_post_mods H ctx func ce cx e es sa sm s0 ee v op t /\
      storage_well_formed_on cx ee (FST H) /\
      expr_store_bound cx (post_value_type ce e) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      ptr_val_ok cx (post_value_type ce e) v op G tn t /\ ptr_buf_ok ce e op G t /\
      ~is_word_type (post_value_type ce e) /\
      evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
      value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
      eval_operand op t = SOME w /\ op_taint tn op = {} /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem) /\
      (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
      w2n w + type_memory_size rt < dimword (:256) /\
      (0 < type_memory_size rt ==>
        ?x. op = Var x /\ not_fresh_at sm x /\ ptr_covers G tn x t (type_memory_size rt)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (`gas_admissible (bind (eval_expr cx (TypeBuiltin dst Convert dst [e]))
         (read_result cx)) expr_res_ok es` by
       (irule eval_expr_force_admissible >> simp[] >>
        rpt strip_tac >> drule_then ACCEPT_TAC eval_expr_type_builtin_value) >>
     drule_then ACCEPT_TAC convert_operand_admissible) >>
  mp_tac convert_operand_buffer_outcome_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
