Theory gasShadowBoolChainOperands
Ancestors
  gasShadow exprLowering vyperAST list

Theorem gas_shadow_literal_eq[local]:
  (gas_shadow_expr e = Literal ty lit) <=> (e = Literal ty lit)
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def]
QED

Theorem gas_shadow_bool_chain_operands:
  !k e. bool_chain_operands d k (gas_shadow_expr e) =
        MAP gas_shadow_expr (bool_chain_operands d k e)
Proof
  Induct_on `k` >> Cases_on `e` >>
  simp[gas_shadow_expr_def, bool_chain_operands_def, gas_shadow_literal_eq] >>
  rpt IF_CASES_TAC >> simp[gas_shadow_expr_def]
QED
