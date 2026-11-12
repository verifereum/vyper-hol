(*
 * pop: the taint bound holds before the length store and is kept through dead_bytes_frame.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   pop_expr_ptr_ok
 *)
Theory bodyPtrPop
Ancestors
  bodyPtrPopCompose bodyPtrPopRootCase
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem pop_expr_ptr_ok:
  !cx v10 bt. body_base_target_ptr_ok cx bt ==> body_expr_ptr_ok cx (Pop v10 bt)
Proof
  rpt strip_tac >> Cases_on `?nid. bt = TopLevelNameTarget nid`
  >- gvs[body_pop_root_ptr_ok] >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop v10 bt) es` by
    (irule pop_vv_ptr_cases >> fs[] >> metis_tac[]) >>
  simp[] >> metis_tac[expr_sim_ptr_of_vv]
QED
