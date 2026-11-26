Theory bodyFullBoolChainOperands
Ancestors
  bodyFullBoolChain bodyFullPreds boolChainOperandsGuarded

Theorem body_expr_full_ok_bool_chain_operands:
  !cx d k e. body_expr_full_ok cx e ==>
    bool_chain_full_ok cx (bool_chain_operands d k e)
Proof
  ntac 2 gen_tac >>
  match_mp_tac (Q.INST [`G` |-> `\c. ?s tv s'. eval_expr cx c s = (INL tv,s')`]
    bool_chain_operands_guarded) >>
  BETA_TAC >> rpt conj_tac
  >- simp[bool_chain_full_ok_def]
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC body_ifexp_children_full_ok)
  >> rw[bool_chain_full_ok_def]
QED
