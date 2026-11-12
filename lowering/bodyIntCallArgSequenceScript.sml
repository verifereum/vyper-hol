(* Counted deferred-result cons sequencing, at the head's actual endpoint. *)
Theory bodyIntCallArgSequence
Ancestors
  bodyIntCallArgCompose vyperInterpreter vyperState gasOutcome gasSummary

Theorem eval_expr_results_cons_then_outcome:
  gas_outcome memory tops (ctx,func) (eval_expr cx e) (es,s0) P
    (\res ee r. ?exc. res = INR exc /\ E exc ee r) /\
  (!left raw mid t.
    gas_marked_exec memory (ctx,func) (eval_expr cx e)
      (es,s0) left (INL raw) mid (OK t) /\
    P (INL raw) (mid with gas_obs := []) t ==>
    gas_outcome memory tops (ctx,func)
      (bind (eval_expr_results cx args) (\raws. k (raw::raws)))
      (mid with gas_obs := [],t) Q
      (\res ee r. ?exc. res = INR exc /\ E exc ee r)) /\
  (!res ee t. P res ee t ==> ?raw. res = INL raw) ==>
  gas_outcome memory tops (ctx,func)
    (bind (eval_expr_results cx (e::args)) k) (es,s0) Q
    (\res ee r. ?exc. res = INR exc /\ E exc ee r)
Proof
  simp[Once evaluate_def, bind_assoc, bind_return] >>
  strip_tac >> irule gas_outcome_bind_result_marked >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
