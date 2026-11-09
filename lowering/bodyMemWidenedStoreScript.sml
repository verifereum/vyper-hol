(* Physical widened-field reads and typed-copy store continuations. *)
Theory bodyMemWidenedStore
Ancestors
  exprSimUnwrapProps exprSimUnwrap exprSimMemorySource
  gasSummary fragGasPathMem fragGasMode loweringPosts vyperState list
  exprSimAggregateChildren exprLowering context emitHelper valueCopyBytes compileEnv

Theorem aggregate_physical_memory_read_mem:
  vv_post ctx func ce cx e es sa sm s0 es' tvv (LocatedValue t p) r /\
  p.ptr_location = LocMemory /\ ~is_word_type t /\ ~r.vs_halted ==>
  ?v. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
        [] (INL v) es' (OK r) /\
    expr_post ctx func ce cx e es sa sm s0 es' v p.ptr_operand r
Proof
  strip_tac >>
  Cases_on `read_result cx tvv es'` >> rename1 `_ = (res,ee)` >>
  `ee = es'` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`)
  >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tvv es' = (INL v,es')` >>
  drule vv_post_read_result >> strip_tac >> gvs[] >>
  qexists_tac `v` >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, cj 1 gas_path_mem_rules] >>
      simp[read_result_gas_obs]) >>
  metis_tac[expr_post_of_vv_post_memory]
QED

Theorem aggregate_widened_memory_read_mem:
  compile_expr ce ty e si = (vv,sj) /\
  post_value_type ce e <> expr_type e /\
  ~is_word_type (post_value_type ce e) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  unwrap_value ce vv sm = (op,su) /\ ~r.vs_halted ==>
  ?v. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
        [] (INL v) es' (OK r) /\
    expr_post ctx func ce cx e es sa sm s0 es' v op r /\ su = sm
Proof
  strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >>
      Cases_on `read_result cx tvv es'` >> rename1 `_ = (res,ee)` >>
      `ee = es'` by metis_tac[read_result_state] >> gvs[] >>
      reverse (Cases_on `res`) >- metis_tac[vv_post_failed_read] >>
      rename1 `read_result cx tvv es' = (INL v,es')` >>
      drule vv_post_read_result >> strip_tac >>
      qexists_tac `v` >> simp[] >> conj_tac
      >- (simp[gas_marked_exec_def, gas_marked_path_def, cj 1 gas_path_mem_rules] >>
          simp[read_result_gas_obs]) >>
      metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  `p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `~is_word_type t` by
    (fs[vv_post_def, vv_holds_def] >>
     metis_tac[is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  drule_all aggregate_physical_memory_read_mem >> simp[]
QED
