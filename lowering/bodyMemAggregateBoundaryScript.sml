(* Memory-counted aggregate traversal boundaries. *)
Theory bodyMemAggregateBoundary
Ancestors
  exprSimMemDefs exprSimWordArgs gasOutcome gasSummary fragGasMode fragGasPathMem

Theorem aggregate_tuple_nil_outcome_mem:
  ~s.vs_halted /\ Q (INL []) (es with gas_obs := []) s ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx []) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, exprSimWordArgsTheory.eval_exprs_nil,
       gas_marked_path_def] >>
  irule (cj 1 gas_path_mem_rules) >> simp[]
QED
