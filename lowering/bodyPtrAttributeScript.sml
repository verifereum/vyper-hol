(*
 * Attributes: a storage place owes ptr_vv_ok's taint bound.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   attribute_expr_ptr_ok
 *)
Theory bodyPtrAttribute
Ancestors
  bodyPtrAttributeSim exprSimAttribute
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem attribute_expr_ptr_ok:
  !cx v9 e id. body_expr_ptr_ok cx e ==> body_expr_ptr_ok cx (Attribute v9 e id)
Proof
  rpt gen_tac >> disch_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  qpat_x_assum `body_expr_ptr_ok cx e`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_ptr_ok_def]) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`d`, `PG`, `func`, `ty`] strip_assume_tac) >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty (Attribute v9 e id) es` by
    (drule_all attribute_vv_sim_ptr >> simp[]) >>
  simp[] >> irule expr_sim_ptr_of_vv >> simp[] >> qexists_tac `env` >> simp[]
QED
