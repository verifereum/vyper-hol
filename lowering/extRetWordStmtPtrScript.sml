Theory extRetWordStmtPtr
Ancestors
  extRetWordStmtPartsPtr extRetWordExprConsumerPtr exprOpenMain
  exprOpenTerminals exprLowering exprSimHypsDefs bodyPtrDefs
  compileEnv loweringPosts vyperInterpreter vyperState finite_map stmtSimReturn

Theorem external_return_lower_value_open:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_body_pre cenv cx env e es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx e es = (INL tv,es1) /\
  lower_value compile_expr cenv aty e sa = (op,sb) /\
  ~block_is_terminated sa ==> ~block_is_terminated sb
Proof
  strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `~block_is_terminated cs'` by
    (irule compile_expr_open_general >> metis_tac[]) >>
  drule_all unwrap_value_open >> simp[]
QED

