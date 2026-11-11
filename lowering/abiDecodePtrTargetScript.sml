(* Body-side interfaces used before entering the memory ABI decoder. *)
Theory abiDecodePtrTarget
Ancestors
  bodyPtrPreds exprOpenFirstOperand supportedProgram supportedExprTraverse
  exprSimHypsDefs vyperAST vyperContext list

Theorem type_builtin_operand_ptr:
  !cx ann tb typ arg args cenv env es d PG tops ctx func ty.
    (type_builtin_args_length_ok tb (LENGTH (arg::args)) ==>
       body_exprs_ptr_ok cx (arg::args)) /\
    type_builtin_args_length_ok tb (LENGTH (arg::args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TypeBuiltin ann tb typ (arg::args)) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty arg es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty arg es
Proof
  rpt strip_tac >>
  `body_expr_ptr_ok cx arg` by gvs[body_exprs_ptr_ok_def] >>
  drule expr_body_pre_type_builtin_head >> strip_tac >>
  gvs[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem abi_decode_body_target_occurs:
  !cenv cx env ann unwrap typ args es.
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode unwrap) typ args) es ==>
    occurs_abi_decode_target typ (cx_tops cx)
Proof
  simp[expr_body_pre_def] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[supported_expr_exists_def, expr_abi_decode_target_root_def]
QED
