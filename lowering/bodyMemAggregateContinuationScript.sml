(* Consumer boundary for an aggregate element's marked read and store. *)
Theory bodyMemAggregateContinuation
Ancestors
  bodyMemAggregateStore bodyMemAggregateUnwrap exprSimMemUnwrap
  exprSimAggregateChildren exprSimMemDefs exprSimUnwrap exprSimUnwrapProps
  loweringPosts exprLowering compileEnv context fragGasPathMem gasSummary
  gasOutcome fragGasMode list

Theorem aggregate_rebased_marked_read_mem_capacity:
  unwrap_value ce vv sm = (op,su) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (is_word_type (expr_type e) ==>
   ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK u) /\
    expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    (~is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e ==>
     !sw tvt. eval_operand op u = SOME sw /\
              evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
              type_memory_size tvt = 0 \/
              w2n sw + type_memory_size tvt <= u.vs_alloca_next) /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ r.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule vv_post_rebase >> strip_tac >>
  `local_ptrs_reserved ce (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved ce sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ _` kall_tac >>
  Cases_on `is_word_type (expr_type e)`
  >- (drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      impl_tac >- simp[] >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_unwrap_value_marked_read_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[]
QED
