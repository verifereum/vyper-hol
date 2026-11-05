(* Source-only bridges for counted mixed word/vv operand composition. *)
Theory exprSimBopRestWordCompose
Ancestors
  gasSummary gasSummaryCompose gasExemptCert exprBopSimProps vyperState
  vyperInterpreter

Theorem rest_word_marked_read:
  gas_marked_exec memory (ctx, func) (eval_expr cx e)
    (es,s0) marks (INL tv) mid (OK t) /\
  (!tail. read_result cx tv (mid with gas_obs := tail) =
    (INL v, mid with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx, func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) mid (OK t)
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  simp[bind_def]
QED
