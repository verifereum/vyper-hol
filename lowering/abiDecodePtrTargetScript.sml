(* Body-side interfaces used before entering the memory ABI decoder. *)
Theory abiDecodePtrTarget
Ancestors
  bodyPtrPreds exprOpenFirstOperand supportedProgram supportedExprTraverse
  exprSimHypsDefs vyperAST vyperContext list

Theorem abi_decode_body_target_occurs:
  !cenv cx env ann unwrap typ args es.
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode unwrap) typ args) es ==>
    occurs_abi_decode_target typ (cx_tops cx)
Proof
  simp[expr_body_pre_def] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[supported_expr_exists_def, expr_abi_decode_target_root_def]
QED
