Theory immutableDeployEmptyFixture
Ancestors
  immutableDeployEmptyProbe exprSimAggregates exprSimHypsDefs

Theorem empty_struct_vv_sim:
  !ctx func cenv cx env ann nsid ty es.
    expr_body_pre cenv cx env (StructLit ann nsid []) es ==>
    expr_vv_sim ctx func cenv cx ty (StructLit ann nsid []) es
Proof
  rpt strip_tac >>
  qspecl_then [`F`, `ctx`, `func`, `cenv`, `cx`, `ann`, `nsid`, `[]`]
    mp_tac compile_struct_lit_vv_case >>
  simp[exprs_case_def, expr_vv_case_def] >>
  disch_then drule >> simp[]
QED
