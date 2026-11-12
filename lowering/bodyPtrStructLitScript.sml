(*
 * Struct literals.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   structlit_expr_ptr_ok
 *)
Theory bodyPtrStructLit
Ancestors
  bodyPtrStructLitSeamUniform bodyPtrStructLitWidened
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem structlit_expr_ptr_ok:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ptr_ok cx (MAP SND kes)) ==>
    body_expr_ptr_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `EVERY (\e. post_value_type cenv e = expr_type e) (MAP SND kes)`
  >- (`body_exprs_ptr_ok cx (MAP SND kes)` by
        (first_assum (qspec_then `MAP FST kes` mp_tac) >> simp[]) >>
      drule_all body_struct_lit_uniform_ptr >>
      disch_then (qspecl_then [`d`, `PG`, `func`, `ty`] assume_tac) >>
      metis_tac[expr_sim_ptr_of_vv]) >>
  irule body_struct_lit_widened_call_elem_ptr >>
  fs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >> metis_tac[]
QED
