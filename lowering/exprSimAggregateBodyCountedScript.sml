(* Replay boundary for body-aware counted aggregate children. *)
Theory exprSimAggregateBodyCounted
Ancestors
  exprSimAggregateChildren exprSimAggregateLoops exprSimSource
  gasSummary fragGasMode vyperInterpreter vyperState
Libs
  monadsyntax

Theorem aggregate_body_marked_replay:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res mid r ==>
  source (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (res,mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem aggregate_body_marked_read_replay:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid r /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) ==>
  expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  (do res <- eval_expr cx e; read_result cx res od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := [])
Proof
  strip_tac >> drule aggregate_body_marked_replay >> strip_tac >>
  simp[bind_def]
QED
