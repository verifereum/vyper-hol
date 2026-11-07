(* The source continuation after concat's operand-list evaluation. *)
Theory bodyMemBiConcatResult
Ancestors
  bodyMemBiConcatArgs bodyMemBiConcatPrefix bodyMemBiConcatFragments
  bodyMemBiECRecoverCompose exprSimConcatResult gasSummary gasOutcome
  fragGasMode fragGasPathMem exprSimMemDefs vyperState vyperValueOperation
  exprSimWordArgs exprSimDefs list

Theorem concat_result_summary_mem[local]:
  evaluate_concat n vs = INL v /\
  gas_path_mem ctx func s 0 (OK t) /\
  Q (INL (Value v)) (ee with gas_obs := []) t ==>
  gas_summary_at T (ctx,func) []
    (\st. ((case evaluate_concat n vs of INL v => INL (Value v)
            | INR err => INR (Error err)), st)) (ee,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value v)`, `ee`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def]
QED
