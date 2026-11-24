(* The calldata slice consumes its unary child's joint judgment. *)
Theory bodyFullBuiltinBytestringCalldataCase
Ancestors
  bodyFullShadowBodyInv bodyFullSimProjection
  bodyFullPreds bodySimFull exprSimCalldataSlice exprSimHypsDefs
  exprLoweringProps exprSimSource builtinProps vyperContext vyperTyping vyperAST list

Theorem calldata_slice_body_operand_full:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  ?e m. args = [e] /\ expr_type e = BaseT (UintT 256) /\
    ann = BaseT (BytesT (Dynamic m)) /\ 0 < n /\ n <= m /\ m < 2 ** 256 /\ n < 2 ** 256 /\
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
  `n < 2 ** 256` by (fs[] >> decide_tac) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> fs[expr_body_pre_def]) >>
  `body_exprs_full_ok cx [e]` by
    (first_x_assum irule >> simp[builtin_args_length_ok_def]) >>
  `body_expr_full_ok cx e` by fs[body_exprs_full_ok_def] >>
  simp[] >>
  irule body_expr_full_ok_simulations >> metis_tac[]
QED
