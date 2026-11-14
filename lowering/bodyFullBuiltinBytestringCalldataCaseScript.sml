(* The calldata slice consumes its unary child's joint judgment. *)
Theory bodyFullBuiltinBytestringCalldataCase
Ancestors
  bodyFullPreds bodySimFull exprSimCalldataSlice exprSimHypsDefs
  exprLoweringProps exprSimSource builtinProps vyperContext vyperTyping vyperAST list

Theorem calldata_slice_body_operand_full:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  ?e. args = [e] /\ expr_type e = BaseT (UintT 256) /\
    ann = BaseT (BytesT (Dynamic n)) /\ 0 < n /\ n < 2 ** 256 /\
    expr_body_pre cenv cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (CalldataSlice n) args)` by
    fs[expr_body_pre_def] >>
  drule calldata_slice_typing >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> fs[expr_body_pre_def]) >>
  `body_exprs_full_ok cx [e]` by
    (first_x_assum irule >> simp[builtin_args_length_ok_def]) >>
  `body_expr_full_ok cx e` by fs[body_exprs_full_ok_def] >>
  simp[] >>
  fs[body_expr_full_ok_def] >> metis_tac[]
QED
