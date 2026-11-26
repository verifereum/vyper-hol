Theory boolChainOperandsSupported
Ancestors
  boolChainOperandsGuarded supportedExprTraverse list

Theorem bool_chain_operands_supported:
  ~supported_expr_exists p e ==>
  EVERY (\child. ~supported_expr_exists p child) (bool_chain_operands d k e)
Proof
  mp_tac (Q.INST [`P` |-> `\e. ~supported_expr_exists p e`,
                  `Q` |-> `EVERY (\child. ~supported_expr_exists p child)`,
                  `G` |-> `\c. T`] bool_chain_operands_guarded) >>
  simp[supported_expr_exists_def]
QED
