Theory bodyPtrIfExpCallAlignment
Ancestors bodyPtrIfExpCallShape bodyPtrIfExpUnwrapContract exprLowering

(* Alignment is needed only in the original operand's normal continuation.
   No claim is made about exceptional or exempt outcomes. *)
Theorem ifexp_positive_call_normal_alignment:
  !ce ret_ty ann fid args dret sa vv sb ret_count rbs pvs ctx fn cx es s0 ee tv t.
    compile_expr ce ret_ty (Call ann (IntCall fid) args dret) sa = (vv,sb) /\
    ce.ce_func_info (nsid_to_string fid) = (ret_count,rbs,pvs) /\
    (0 < ret_count \/ 0 < rbs) /\
    vv_post ctx fn ce cx (Call ann (IntCall fid) args dret)
      es sa sb s0 ee tv vv t ==>
    lowered_value_type ce (Call ann (IntCall fid) args dret) =
      expr_type (Call ann (IntCall fid) args dret)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_component_eq] >> strip_tac >>
  Cases_on `ret_count = 0`
  >- (gvs[] >> drule_all compile_call_intcall_buffer_shape >> strip_tac >>
      gvs[] >> drule vv_post_located_type >> simp[lowered_value_type_def]) >>
  `0 < ret_count` by decide_tac >>
  drule_all compile_call_intcall_stack_shape >> strip_tac >> gvs[] >>
  drule vv_post_located_type >> simp[lowered_value_type_def]
QED

Theorem ifexp_buffer_call_normal_alignment:
  !ce ret_ty ann fid args dret sa vv sb rbs pvs ctx fn cx es s0 ee tv t.
    compile_expr ce ret_ty (Call ann (IntCall fid) args dret) sa = (vv,sb) /\
    ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs /\
    vv_post ctx fn ce cx (Call ann (IntCall fid) args dret)
      es sa sb s0 ee tv vv t ==>
    lowered_value_type ce (Call ann (IntCall fid) args dret) =
      expr_type (Call ann (IntCall fid) args dret)
Proof
  rpt strip_tac >> irule ifexp_positive_call_normal_alignment >>
  conj_tac >- (qexistsl_tac [`pvs`, `rbs`, `0`] >> simp[]) >>
  metis_tac[]
QED
