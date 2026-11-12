(* Authorized containing windows for tuple selection. *)
Theory bodyIntCallFamAggSubscriptTuple
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore exprSimTuple
  valueEncoding words context

Theorem intcall_tuple_element_window:
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee q /\
  expr_sim_inv ce fp.jc_cx env es /\
  vv_at ce fp.jc_cx (TupleT tys) sa sn ee tv bvv q /\
  read_result fp.jc_cx tv ee = (INL (ArrayV (TupleV vs)),ee) /\
  eval_operand (vv_operand bvv) q = SOME w /\ vv_loc bvv = LocMemory /\
  OPT_MMAP (evaluate_type (get_tenv fp.jc_cx)) tys = SOME tvs /\
  evaluate_type (get_tenv fp.jc_cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\
  eval_operand dst q = SOME (w + n2w (tuple_offset ce tys LocMemory k)) /\
  a <= w2n w /\ w2n w + type_memory_size (TupleTV tvs) <= a + len /\
  a + len < dimword (:256) /\
  (fp.jc_lo <= a \/
   ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z) ==>
  ?cw. eval_operand dst q = SOME cw /\
    a <= w2n cw /\ w2n cw + type_memory_size (EL k tvs) <= a + len /\
    a + len < dimword (:256) /\
    (fp.jc_lo <= a \/
     ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)
Proof
  strip_tac >> drule_all tuple_elem_ptr >> strip_tac >>
  qexists_tac `w + n2w (tuple_offset ce tys LocMemory k)` >>
  fs[valueEncodingTheory.type_memory_size_def] >> metis_tac[]
QED
