(* Reachability interface for the conditional aggregate children predicate. *)
Theory bodyMemAggregateLoopBoundary
Ancestors
  bodyMemoryPreds gasSummary

Theorem aggregate_body_exprs_mem_tail:
  body_exprs_mem_ok cx (e::args) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s)
    marks (INL tv) ee (OK r) /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (ee,r)
    [] (INL v) ee' (OK q) ==>
  body_exprs_mem_ok cx args
Proof
  simp[body_exprs_mem_ok_def, gas_marked_exec_def] >>
  rpt strip_tac >>
  first_x_assum irule >>
  metis_tac[]
QED
