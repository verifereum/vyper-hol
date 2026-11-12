(* Successful tuple selection at a counted base endpoint. *)
Theory bodyIntCallFamAggSubscriptTupleSource
Ancestors
  bodyIntCallFamAggSubscriptTuple exprSimTuple stmtReasonVvMemory vyperTyping

Theorem intcall_tuple_source_selection:
  expr_body_pre ce cx env
    (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  expr_body_pre ce cx env obj es /\ expr_type obj = TupleT tys /\
  k < LENGTH tys /\ eval_expr cx obj es = (INL btv,ee) /\
  vv_post ctx func ce cx obj es sa sm s0 ee btv bvv t ==>
  ?tvs vs selected.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    LENGTH tvs = LENGTH tys /\ values_have_types tvs vs /\
    LENGTH vs = LENGTH tvs /\
    read_result cx btv ee = (INL (ArrayV (TupleV vs)),ee) /\
    select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee =
      (INL selected,ee) /\
    read_result cx selected ee = (INL (EL k vs),ee)
Proof
  strip_tac >> drule_all tuple_base_facts >> strip_tac >>
  drule vv_post_read_ok >> strip_tac >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  `?vs. v = ArrayV (TupleV vs) /\ values_have_types tvs vs` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
     Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  Cases_on `select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee` >>
  metis_tac[select_tuple_read]
QED
