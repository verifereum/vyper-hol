Theory bodyFullBuiltinWordNot
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame exprSimWordBuiltins exprSimHypsDefs
  exprSimUnopProps exprSimUnopCompose gasOutcomeFullCompose
  fragGasSeqPtr exprSimSource
  vyperTypeSystem vyperTyping vyperAST list

Theorem word_not_pre[local]:
  expr_body_pre cenv cx env (Builtin ann Not args) es ==>
  ?e. args = [e] /\ ann = expr_type e /\
      expr_body_pre cenv cx env e es /\
      (is_bool_type ann \/ is_uint256_type ann \/
       is_bytes32_type ann \/ is_flag_type ann)
Proof
  strip_tac >>
  `well_typed_builtin_app ann Not (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >>
  (irule expr_body_pre_builtin_arg >> simp[] >>
   conj_tac >- gvs[expr_body_pre_def] >>
   qexistsl_tac [`expr_type h`, `[h]`, `Not`, `es`] >> simp[])
QED
