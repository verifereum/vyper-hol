(* Marked prefix composition for external-call continuations. *)
Theory extCallSeamSummary
Ancestors
  extCallSeamPrecheck gasSummary gasSummaryCompose fragGasMode
  loweringPosts vyperState list

Theorem extcall_summary_bind_normal:
  gas_marked_exec F (ctx,func) source (es,s) left (INL v) mid (OK t) /\
  (?right. gas_summary_at F (ctx,func) right (k v)
    (mid with gas_obs := [],t) Q R) ==>
  ?marks. gas_summary_at F (ctx,func) marks (bind source k) (es,s) Q R
Proof
  simp[gas_summary_at_def] >> rpt strip_tac >>
  drule_all gas_marked_exec_bind_normal >> strip_tac >>
  qexists_tac `left ++ right` >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem extcall_summary_bind_exception:
  gas_marked_exec F (ctx,func) source (es,s) marks (INR exc) fin r /\
  exit_result r /\ R (INR exc) (fin with gas_obs := []) r ==>
  gas_summary_at F (ctx,func) marks (bind source k) (es,s) Q R
Proof
  strip_tac >> drule gas_marked_exec_bind_exception >>
  disch_then (qspec_then `k` assume_tac) >>
  simp[gas_summary_at_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_marked_prefix:
  (!tail. source (es with gas_obs := tail) =
     (res, fin with gas_obs := tail)) /\ gas_path ctx func s n r ==>
  gas_marked_exec F (ctx,func) source (es,s) (REPLICATE n F) res fin r
Proof
  strip_tac >> irule gas_marked_exec_no_source_read >>
  simp[gas_marked_path_def]
QED
