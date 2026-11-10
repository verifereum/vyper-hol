(* Successful aggregate heads: source facts and typed-store continuation. *)
Theory bodyMemAggregateHeadContinuation
Ancestors
  bodyMemAggregateLoopFrames bodyMemAggregateBodyCons bodyMemAggregateLoopBoundary
  exprSimHyps bodySim exprSimAggregateChildren exprSimAggregateLoops
  exprLoweringProps compileEnv loweringPosts fragGasPathMem vyperState
  gasSummary gasOutcome fragGasMode fragGasPath freshWrites exprSimHypsDefs

Theorem aggregate_body_head_continuation_mem:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  expr_body_pre ce cx env e es /\ body_exprs_mem_ok cx (e::args) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),ss) /\
  ci_mono sa sm /\ local_ptrs_reserved ce sa /\ fn_has_code sm ss func /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  stmt_state_rel ctx func ce cx es s0 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME htv /\
  off + type_memory_size htv <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size htv)) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) es1 (OK t1) /\ es1.gas_obs = [] /\
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es1 tv vv t1 /\
  t1.vs_current_bb = sm.cs_current_bb /\
  t1.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t1 ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1)
      [] (INL v) es1 (OK q) /\
    val_in_memory htv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es1 q /\
    (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
    (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!name lb len. local_region ce es1.scopes t1 name lb len ==>
        lo+sz <= lb \/ lb+len <= lo) /\
      lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
    locals_kept ce es1 t1 q /\ q.vs_current_bb = ss.cs_current_bb /\
    q.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func q /\ t1.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\
    FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
    expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\
    value_has_type htv v /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory
Proof
  strip_tac >>
  `es1 with gas_obs := [] = es1` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule_all aggregate_tuple_marked_child_source_any >> simp[] >> strip_tac >>
  `~t1.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size htv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `lookup_var x t1 = SOME (n2w b) /\
   FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz) /\
   stmt_state_rel ctx func ce cx es1 t1` by (fs[vv_post_def] >> metis_tac[]) >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `alloca_inv t1` by fs[stmt_state_rel_def] >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
    lo+sz <= b+off \/ b+off+type_memory_size htv <= lo` by
    (rpt strip_tac >> metis_tac[aggregate_alloca_slice_excludes_local]) >>
  `mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory` by
    (irule vv_post_old_buffer >> goal_assum (drule_at Any) >>
     qexists `inst.inst_id` >> simp[] >> rpt strip_tac >>
     mp_tac (GEN_ALL (Q.INST [`off` |-> `0`, `n` |-> `asz`]
       (SPEC_ALL aggregate_alloca_slice_excludes_local))) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) aggregate_tuple_marked_footprint_any >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ce.ce_is_ctor ==> _`)) >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) aggregate_body_cons_continuation_mem_cursor >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ t1 = SOME _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  disch_then (qspecl_then [`asz`, `inst.inst_id`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[body_inv_def, expr_sim_inv_def] >>
    metis_tac[arithmeticTheory.ADD_COMM])) >> strip_tac >>
  `body_exprs_mem_ok cx args` by metis_tac[aggregate_body_exprs_mem_tail] >>
  qexistsl_tac [`v`, `q`] >> simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac >- gvs[] >>
  qpat_x_assum `!v. read_result _ _ _ = _ ==> _` irule >>
  qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED
