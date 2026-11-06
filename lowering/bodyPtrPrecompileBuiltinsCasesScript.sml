Theory bodyPtrPrecompileBuiltinsCases
Ancestors bodyPtrPreds exprSimHypsDefs vyperTypeSystem vyperInterpreter vyperContext list

Theorem precompile_body_pre_arity:
  (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
  expr_body_pre cenv cx env (Builtin ty bt es) st ==>
  builtin_args_length_ok bt (LENGTH es)
Proof
  rw[expr_body_pre_def, well_typed_expr_def,
     well_typed_builtin_app_def, builtin_args_length_ok_def] >>
  gvs[well_typed_builtin_app_def, builtin_args_length_ok_def]
QED

Theorem precompile_bad_arity_ptr:
  (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
  ~builtin_args_length_ok bt (LENGTH es) ==>
  body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rw[body_expr_ptr_ok_def] >>
  metis_tac[precompile_body_pre_arity]
QED
