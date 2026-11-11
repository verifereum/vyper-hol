Theory makeSsaRfRenameTrace
Ancestors makeSsaCurrentAllocation makeSsaCurrentRenameTrace
  makeSsaRfAllocation makeSsaDefs makeSsaCurrentProps
  venomInst list alist pair combin


























Theorem current_outputs_trace_owned:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_env_owned V H E ==> current_env_owned V H' E'
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[current_env_owned_push]
QED

Theorem current_inst_trace_owned:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_env_owned V H E ==> current_env_owned V H' E'
Proof
  simp[current_inst_trace_def] >> metis_tac[current_outputs_trace_owned]
QED

Theorem current_local_trace_owned:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_env_owned V H E ==> current_env_owned V H' E'
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[current_inst_trace_owned]
QED

Theorem current_local_trace_exit_separation:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_owned V H E /\ MEM v V /\ MEM w V /\ v <> w ==>
  latest_current_name rs' v <> latest_current_name rs' w
Proof
  rpt strip_tac >> drule_all current_local_trace_preserves >> strip_tac >>
  drule_all current_local_trace_owned >> strip_tac >>
  fs[current_allocation_consistent_def] >>
  metis_tac[current_latest_name_separation]
QED
