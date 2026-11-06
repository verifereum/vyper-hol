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

Theorem body_expr_ptr_frame:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem body_exprs_ptr_head:
  body_exprs_ptr_ok cx (e::es) ==> body_expr_ptr_ok cx e
Proof
  simp[body_exprs_ptr_ok_def]
QED

Theorem body_exprs_ptr_tail_force:
  body_exprs_ptr_ok cx (e::es) /\
  (bind (eval_expr cx e) (read_result cx)) s = (INL v,t) ==>
  body_exprs_ptr_ok cx es
Proof
  rw[body_exprs_ptr_ok_def, vyperStateTheory.bind_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED
