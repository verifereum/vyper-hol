Theory boolChainOpsCong
Ancestors
  exprLowering vyperAST list

Theorem compile_bool_chain_ops_lower_value_cong:
  (!e. MEM e es ==>
       lower_value f ce1 (BaseT BoolT) e = lower_value g ce2 (BaseT BoolT) e) ==>
  compile_bool_chain_ops f ce1 d r exit_lbl es =
  compile_bool_chain_ops g ce2 d r exit_lbl es
Proof
  Induct_on `es` >- simp[compile_bool_chain_ops_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  `compile_bool_chain_ops f ce1 d r exit_lbl es =
   compile_bool_chain_ops g ce2 d r exit_lbl es` by simp[] >>
  Cases_on `es` >> once_rewrite_tac[compile_bool_chain_ops_def] >>
  asm_rewrite_tac[]
QED
