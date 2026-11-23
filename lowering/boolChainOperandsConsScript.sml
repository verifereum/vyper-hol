Theory boolChainOperandsCons
Ancestors
  exprLowering vyperAST

Theorem bool_chain_operands_cons:
  !d k e. ?hd hs. bool_chain_operands d k e = hd::hs
Proof
  rpt gen_tac >> Cases_on `k`
  >- simp[bool_chain_operands_def] >>
  Cases_on `e` >> simp[bool_chain_operands_def] >>
  rpt IF_CASES_TAC >> simp[]
QED
