Theory vyperLogPreservation

Ancestors
  vyperCall

Definition log_extends_def:
  log_extends (st:evaluation_state) (st':evaluation_state) <=>
    isPREFIX st.logs st'.logs
End

Theorem log_extends_refl:
  log_extends st st
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_trans:
  log_extends st st1 /\ log_extends st1 st2 ==> log_extends st st2
Proof
  simp[log_extends_def] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem log_extends_eq_logs:
  st.logs = st'.logs ==> log_extends st st'
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_append:
  log_extends st (st with logs := st.logs ++ events)
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem return_log_extends[local]:
  return x st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.return_def, log_extends_refl]
QED

Theorem raise_log_extends[local]:
  raise e st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.raise_def, log_extends_refl]
QED

Theorem push_log_log_extends[local]:
  push_log ev st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[push_log_logs] >> simp[log_extends_append]
QED

Theorem append_logs_log_extends[local]:
  append_logs events st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[append_logs_logs] >> simp[log_extends_append]
QED

Theorem bind_log_extends[local]:
  (!r st1. f st = (r,st1) ==> log_extends st st1) /\
  (!x st1 r st2.
     f st = (INL x,st1) /\ g x st1 = (r,st2) ==>
     log_extends st1 st2) /\
  bind f g st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  Cases_on `f st` >>
  gvs[vyperStateTheory.bind_def] >>
  Cases_on `q` >> gvs[] >>
  metis_tac[log_extends_trans]
QED

val _ = export_theory();
