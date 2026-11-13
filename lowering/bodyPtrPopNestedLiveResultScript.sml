Theory bodyPtrPopNestedLiveResult
Ancestors bodyPtrPopNestedLivePost bodyPtrDefs exprSimProps ptrDiscipline
  venomState valueEncoding context words

Theorem pop_result_ptr_mem_ok:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_var out s = SOME w /\ ptr_covers G tn out s (type_memory_size tv) /\
  val_wf tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_mem_ok cx ty v (Var out) G tn s
Proof
  strip_tac >> simp[ptr_mem_ok_def, eval_operand_def] >>
  drule val_store_size_le >> strip_tac >>
  fs[ptr_covers_def] >> rpt strip_tac >> gvs[]
QED

Theorem pop_result_ptr_vv_ok:
  read_result cx result es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_var out s = SOME w /\ ptr_covers G tn out s (type_memory_size tv) /\
  val_wf tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_vv_ok cx ty result (LocatedValue ty (mk_ptr (Var out) LocMemory)) es G tn s
Proof
  strip_tac >>
  `ptr_mem_ok cx ty v (Var out) G tn s` by
    (drule_all pop_result_ptr_mem_ok >> simp[]) >>
  simp[ptr_vv_ok_def, mk_ptr_def] >>
  fs[ptr_covers_def] >> metis_tac[]
QED

Theorem pop_result_ptr_buf_ok:
  ptr_covers G tn out s span /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= span ==>
  ptr_buf_ok cenv e (Var out) G s
Proof
  simp[ptr_covers_def, ptr_buf_ok_def, eval_operand_def] >>
  rpt strip_tac >> qexistsl_tac [`b`, `sz'`] >> gvs[]
QED
