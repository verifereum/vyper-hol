(* Memory-counted aggregate traversal boundaries. *)
Theory bodyMemAggregateBoundary
Ancestors
  exprSimMemDefs exprSimWordArgs gasOutcome gasSummary fragGasMode fragGasPathMem

Theorem aggregate_tuple_nil_outcome_mem:
  ~s.vs_halted /\ Q (INL []) (es with gas_obs := []) s ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx []) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, exprSimWordArgsTheory.eval_exprs_nil,
       gas_marked_path_def] >>
  irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Theorem aggregate_vv_memory_capacity:
  vv_store_bound cx t lt es tv (LocatedValue vt p) s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) lt = SOME ftv /\
  eval_operand p.ptr_operand s = SOME w ==>
  type_memory_size ftv = 0 \/
  w2n w + type_memory_size ftv <= s.vs_alloca_next
Proof
  simp[vv_store_bound_def] >> metis_tac[]
QED

Theorem aggregate_operand_capacity_transport:
  eval_operand op s = SOME w /\
  (n = 0 \/ w2n w + n <= s.vs_alloca_next) /\
  eval_operand op u = eval_operand op s /\
  s.vs_alloca_next <= u.vs_alloca_next ==>
  eval_operand op u = SOME w /\
  (n = 0 \/ w2n w + n <= u.vs_alloca_next)
Proof
  rpt strip_tac >> gvs[]
QED
