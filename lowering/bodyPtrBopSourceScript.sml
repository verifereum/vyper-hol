Theory bodyPtrBopSource
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprBopSimProps exprSimOperators
  gasExemptCert vyperState vyperInterpreter vyperTypeBuiltins exprBopSimDefs
  exprSimDefs vyperValueOperation vyperContext


Theorem bop_typed_source_result_ok:
  well_typed_binop ann bop t1 t2 /\
  evaluate_type (get_tenv cx) ann = SOME tvr /\
  evaluate_type (get_tenv cx) t1 = SOME tv1 /\
  evaluate_type (get_tenv cx) t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 ==>
  expr_res_ok (bop_result cx ann bop [t1;t2] v1 v2 es)
Proof
  strip_tac >>
  `!msg. evaluate_builtin cx es.accounts ann (Bop bop) [t1;t2] [v1;v2] <>
    INR (TypeError msg)` by
    (simp[evaluate_builtin_def] >>
     metis_tac[well_typed_binop_no_type_error]) >>
  simp[bop_result_def] >>
  Cases_on `evaluate_builtin cx es.accounts ann (Bop bop) [t1;t2] [v1;v2]` >>
  simp[expr_res_ok_def] >> Cases_on `y` >> gvs[]
QED
