Theory exprSimNamesBuiltinTyping
Ancestors
  exprSimHypsDefs vyperTypeSystem vyperAST

Theorem non_uint256_not_names_builtin:
  !bi args env ty. well_typed_expr env (Builtin ty bi args) /\
    ty <> BaseT (UintT 256) ==> ~names_builtin bi args
Proof
  recInduct names_builtin_ind >>
  simp[names_builtin_def] >>
  rpt conj_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def]
QED
