(* Counted source boundary for body-aware aggregate child stores. *)
Theory exprSimAggregateBodyCountedChildren
Ancestors
  exprSimAggregateChildren exprSimSource gasSummary vyperState
Libs
  monadsyntax

(* A marked execution replays at the explicit observations selected by its
   target path.  It need not replay at the original state's observations. *)
Theorem aggregate_body_marked_read_source:
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid r /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) ==>
  (do res <- eval_expr cx e; read_result cx res od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  gvs[] >> simp[bind_def]
QED
