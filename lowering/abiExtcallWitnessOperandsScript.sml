(* Original universally quantified operand premises, independent of entry state. *)
Theory abiExtcallWitnessOperands
Ancestors
  abiExtcallWitnessRecords abiExtcallWitnessProbe abiExtcallWrapReachProbe
  exprSimHyps exprSimHypsDefs exprSimLeaves

Theorem witness_operand_cases:
  exprs_case T ctx func witness_cenv witness_cx [witness_target] /\
  exprs_case T ctx func witness_cenv witness_cx [witness_gas]
Proof
  conj_tac >> irule exprs_case_every_ok >>
  simp[witness_target_def, witness_gas_def, compile_literal_case_sim]
QED

Theorem witness_case_antecedent:
  exprs_case T ctx func witness_cenv witness_cx
    (TAKE 1 [witness_target; witness_gas]) /\
  (!s target t.
    eval_exprs witness_cx (TAKE 1 [witness_target; witness_gas]) s = (INL target,t) ==>
    results_case T ctx func witness_cenv witness_cx
      (TAKE (LENGTH (FST (SND ("probe",[],reach_return))))
        (DROP 1 [witness_target;witness_gas]))) /\
  (!s target t s' results t'.
    eval_exprs witness_cx (TAKE 1 [witness_target;witness_gas]) s = (INL target,t) /\
    eval_expr_results witness_cx
      (TAKE (LENGTH (FST (SND ("probe",[],reach_return))))
        (DROP 1 [witness_target;witness_gas])) s' = (INL results,t') ==>
    exprs_case T ctx func witness_cenv witness_cx
      (DROP (1 + LENGTH (FST (SND ("probe",[],reach_return))))
        [witness_target;witness_gas]))
Proof
  simp[results_case_def, witness_operand_cases]
QED
