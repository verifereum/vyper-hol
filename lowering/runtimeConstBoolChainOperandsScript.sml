Theory runtimeConstBoolChainOperands
Ancestors
  boolChainOperandsGuarded vyperTypeContract list

Theorem runtime_constant_bool_chain_operands:
  runtime_constant_expr mods e ==>
  EVERY (runtime_constant_expr mods) (bool_chain_operands d k e)
Proof
  mp_tac (Q.INST [`P` |-> `runtime_constant_expr mods`,
                  `Q` |-> `EVERY (runtime_constant_expr mods)`,
                  `G` |-> `\c:expr. T`] bool_chain_operands_guarded) >>
  simp[runtime_constant_expr_def]
QED
