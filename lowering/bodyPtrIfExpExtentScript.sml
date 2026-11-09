Theory bodyPtrIfExpExtent
Ancestors
  exprSimIfExp exprSimHyps valueEncodingTyping exprSimProps bodyPtrDefs

Theorem ifexp_read_store_extent:
  !ce cx env es result v es' dv.
    expr_sim_inv ce cx env es /\ expr_body_pre ce cx env result es /\
    (do r <- eval_expr cx result; read_result cx r od) es = (INL v,es') /\
    evaluate_type (get_tenv cx) (expr_type result) = SOME dv ==>
    val_store_size dv v <= type_memory_bytes ce (expr_type result)
Proof
  rpt strip_tac >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >> gvs[] >>
  drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  drule val_store_size_le >>
  metis_tac[expr_sim_inv_memory_size]
QED

Theorem ifexp_buffer_store_coverage:
  !ce arm op G s dv v w.
    ptr_buf_ok ce arm op G s /\ eval_operand op s = SOME w /\
    val_store_size dv v <= type_memory_bytes ce (lowered_value_type ce arm) /\
    val_footprint dv v <> 0 ==>
    ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      b <= w2n w /\ w2n w + val_store_size dv v <= b + sz
Proof
  rpt strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce arm) <> 0` by
    (mp_tac (Q.SPECL [`dv`, `v`] val_footprint_le_store_size) >> decide_tac) >>
  gvs[ptr_buf_ok_def] >> first_x_assum drule >> simp[] >>
  strip_tac >> qexistsl [`x`, `b`, `sz`] >> simp[] >> decide_tac
QED
