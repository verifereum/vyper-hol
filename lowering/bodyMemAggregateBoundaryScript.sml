(* Memory-counted aggregate traversal boundaries. *)
Theory bodyMemAggregateBoundary
Ancestors
  exprSimMemDefs exprSimWordArgs gasOutcome gasSummary fragGasMode fragGasPathMem

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
