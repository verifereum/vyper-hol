Theory convertScalarSim
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimConvert exprSimUnop convertScalarTyping exprSimOps
   exprSimHyps exprLowering compileEnv vyperAST freshWrites fragExec exprLoweringProps

Theorem scalar_convert_sim_to_vv:
  !ctx func cenv cx ty ann t e1 es.
    expr_sim ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es ==>
    expr_vv_sim ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  rpt strip_tac >> irule expr_vv_sim_stack >> simp[compile_convert_stack] >>
  metis_tac[eval_expr_type_builtin_value]
QED
