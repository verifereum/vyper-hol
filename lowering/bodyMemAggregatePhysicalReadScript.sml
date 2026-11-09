(* A widened internal-call result unwraps at its physical memory type. *)
Theory bodyMemAggregatePhysicalRead
Ancestors
  bodyMemAggregateContinuation exprSimAggregateSource exprSimAggregateChildren
  exprSimMemorySource exprSimUnwrapProps exprSimUnwrap exprLowering exprSimMemDefs loweringPosts
  compileEnv context fragGasPathMem fragGasMode gasSummary vyperInterpreter
  vyperState venomState valueCopyBytes typedMemoryCopy exprSimHyps exprSimHypsDefs

Theorem aggregate_unequal_post_read_path_mem[local]:
  compile_expr ce ty e si = (vv,sj) /\
  post_value_type ce e <> expr_type e /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ ~r.vs_halted /\
  r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
        [] (INL v) es' (OK r) /\
    expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op r /\
    r.vs_current_bb = su.cs_current_bb /\
    r.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func r /\
    (!tvt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt /\
      eval_operand op r = SOME w ==>
      type_memory_size tvt = 0 \/ w2n w + type_memory_size tvt <= r.vs_alloca_next)
Proof
  strip_tac >>
  `~is_word_type (post_value_type ce e)` by
    (gvs[expr_body_pre_def] >>
     metis_tac[post_value_type_widens, return_source_word_widens_eq]) >>
  drule vv_post_materialises >> strip_tac >>
  drule_all vv_post_materialise >> strip_tac >>
  drule vv_post_rebase >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[post_value_type_word] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists `v` >> simp[] >>
      conj_tac
      >- simp[gas_marked_exec_def, gas_marked_path_def,
           cj 1 gas_path_mem_rules, read_result_gas_obs] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      fs[vv_store_bound_def] >> metis_tac[]) >>
  rename1 `LocatedValue vt p` >>
  `p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `~is_word_type vt` by
    (fs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def] >> qexists `v` >> simp[] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def,
       cj 1 gas_path_mem_rules, read_result_gas_obs] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  fs[vv_store_bound_def] >> metis_tac[]
QED

Theorem aggregate_body_rebased_marked_read_mem_capacity:
  compile_expr ce ty e si = (vv,sj) /\ expr_body_pre ce cx env e es /\
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
  alloca_history func r /\ ~r.vs_halted /\
  r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK u) /\
    expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op u /\
    (post_value_type ce e = expr_type e ==>
     expr_store_bound cx (expr_type e) v op u) /\
    (~is_word_type (post_value_type ce e) /\
     (post_value_type ce e <> expr_type e \/ lowered_value_type ce e = expr_type e) ==>
     !tvt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt /\
       eval_operand op u = SOME w ==>
       type_memory_size tvt = 0 \/ w2n w + type_memory_size tvt <= u.vs_alloca_next) /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ r.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- (drule_all aggregate_rebased_marked_read_mem_capacity >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[] >> metis_tac[]) >>
  drule_all aggregate_unequal_post_read_path_mem >> strip_tac >>
  qexistsl_tac [`v`, `r`] >> simp[]
QED
