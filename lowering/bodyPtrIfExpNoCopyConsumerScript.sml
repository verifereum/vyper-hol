Theory bodyPtrIfExpNoCopyConsumer
Ancestors
  bodyPtrIfExpExtent bodyPtrIfExpInterpretation bodyPtrIfExpMemoryTransport

Theorem ifexp_read_no_copy_ptr_mem_ok:
  !ce cx env es result v es' st sv arm op G tn s.
    expr_sim_inv ce cx env es /\ expr_body_pre ce cx env result es /\
    (do r <- eval_expr cx result; read_result cx r od) es = (INL v,es') /\
    evaluate_type (get_tenv cx) st = SOME sv /\
    type_widens_to (get_tenv cx) st (expr_type result) /\
    punnable ce st (expr_type result) /\
    type_memory_bytes ce (lowered_value_type ce arm) =
      type_memory_bytes ce (expr_type result) /\
    ptr_mem_ok cx st v op G tn s /\ ptr_buf_ok ce arm op G s ==>
    ptr_mem_ok cx (expr_type result) v op G tn s
Proof
  rpt strip_tac >> irule ptr_mem_ok_transport >>
  reverse conj_tac
  >- (qexists_tac `st` >> simp[] >>
      metis_tac[ifexp_type_widens_in_memory]) >>
  rpt strip_tac >>
  drule_all ifexp_read_store_extent >> strip_tac >>
  irule ifexp_buffer_store_coverage >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
