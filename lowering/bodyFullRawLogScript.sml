(*
 * raw_log over the finite-horizon joint judgment: the topics, the data
 * operand and the LOG share one origin/memory/pointer witness.
 *
 * The two shadow-compile premises are the lower_value and
 * compile_multi_exprs forms of the gas-shadow compile spine
 * (gas_shadow_compiles_lower_value with gas_shadow_compile_expr, and
 * gas_shadow_compiles_multi_exprs), which this base doesn't carry yet;
 * body_raw_log_case_full discharges them once it does.
 *
 * TOP-LEVEL:
 *   raw_log_expr_full_ok
 *)
Theory bodyFullRawLog
Ancestors
  bodyFullPreds bodySimFull gasShadowState gasShadow exprLowering
  vyperAST list

val _ = Parse.hide "body";

Theorem raw_log_expr_full_ok:
  !cx ann es dflt.
    (!cenv ty e.
       gas_shadow_compiles (lower_value compile_expr cenv ty e)
         (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
    (!cenv xs.
       gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
         (compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr xs))) /\
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ann RawLog es dflt)
Proof
  cheat
QED
