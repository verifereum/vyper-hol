(* Safe exiting runs transfer backwards through a memory continuation. *)
Theory memContinuationExit
Ancestors
  memContinuation fragExec memSafeRun

Theorem mem_cont_sim_exit_run:
  mem_cont_sim ctx fn s t /\ run_from fuel ctx fn t = r /\
  exit_result r /\ mem_safe_run fuel ctx fn t ==>
  ?fuel'. run_from fuel' ctx fn s = r /\ mem_safe_run fuel' ctx fn s
Proof
  simp[mem_cont_sim_def] >> rpt strip_tac >>
  `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[]
QED

Theorem mem_cont_sim_safe_exit:
  mem_cont_sim ctx fn s t /\
  (?fuel r. run_from fuel ctx fn t = r /\ exit_result r /\
            mem_safe_run fuel ctx fn t) ==>
  ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
           mem_safe_run fuel ctx fn s
Proof
  metis_tac[mem_cont_sim_exit_run]
QED
