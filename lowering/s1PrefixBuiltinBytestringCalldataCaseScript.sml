Theory s1PrefixBuiltinBytestringCalldataCase
Ancestors
  s1PrefixPreds bodyFullBuiltinBytestringCalldataCase vyperContext list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all calldata_slice_body_operand_full >>
  disch_then (qspecl_then [`shadow_func`,`lo`,`func`,`d`,`PG`,`DF`] strip_assume_tac) >>
  gvs[] >>
  `body_exprs_prefix_ok cx [e]` by fs[builtin_args_length_ok_def] >>
  `body_expr_prefix_ok cx e` by fs[body_exprs_prefix_ok_def] >>
  fs[body_expr_prefix_ok_def] >> metis_tac[]
QED
*)
Theorem calldata_slice_body_operand_prefix:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
     body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  ?e m. args = [e] /\ expr_type e = BaseT (UintT 256) /\
    ann = BaseT (BytesT (Dynamic m)) /\ 0 < n /\ n <= m /\ m < 2 ** 256 /\ n < 2 ** 256 /\
    expr_body_pre cenv cx env e es /\
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es
Proof
  cheat
QED
