Theory bodyPtrIfExpExtent
Ancestors
  exprSimIfExp exprSimHyps valueEncodingTyping exprSimProps

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
