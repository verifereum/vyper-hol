(* Capacity interfaces for allocated aggregate buffers, including reused sites. *)
Theory bodyMemAggregateBounds
Ancestors
  bodyAllocMemory bodyMemAggregateSide exprSimMemDefs fragExecMem
  exprSimHypsDefs loweringPosts venomMemDefs venomState words exprLoweringProps

Theorem aggregate_alloca_capacity_mem:
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= s.vs_alloca_next
Proof
  simp[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem aggregate_alloc_buffer_entry_mem:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ ~block_is_terminated sa ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    frag_exec_mem ctx sa sm
      (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s /\ alloca_history func s)
      (\t. ?b. stmt_state_rel ctx func ce cx es t /\
        eval_operand buf.buf_operand t = SOME (n2w b) /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
        b + sz < dimword (:256) /\ b + sz <= t.vs_alloca_next /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next) R
Proof
  strip_tac >> drule_all compile_alloc_buffer_body_frag_mem >>
  disch_then (qspecl_then [`s0`, `es`, `cx`, `ctx`, `R`] strip_assume_tac) >>
  qexistsl_tac [`inst`, `x`] >> simp[] >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> qexists_tac `t` >> simp[eval_operand_def] >>
      drule_all aggregate_alloca_capacity_mem >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem aggregate_allocated_result_store_bound_mem:
  vv_post ctx func ce cx e es sa sb s0 es' tv
    (LocatedValue (expr_type e) p) t /\
  lowered_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
  eval_operand p.ptr_operand t = SOME (n2w b) /\
  alloca_inv t /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  type_memory_size ftv <= sz /\ b + sz < dimword (:256) ==>
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tv
    (LocatedValue (expr_type e) p) t
Proof
  strip_tac >> simp[] >> drule vv_store_bound_capacity >>
  disch_then irule >> simp[] >> disj2_tac >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  `b + sz <= t.vs_alloca_next` by metis_tac[] >> decide_tac
QED
