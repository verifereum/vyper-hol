Theory dftTerminalResult
Ancestors
  dftOpenMachine o1PassContract unitTransformDefs stateEquiv

Theorem dft_materialized_terminal_dead_result_rel:
  ((?s. rr = Halt s) \/ (?a s. rr = Abort a s)) ==>
  dead_result_rel D
    (dft_open_materialize_result xs n rr)
    (dft_open_materialize_result ys m rr)
Proof
  strip_tac >> irule unit_result_rel_dead_result_rel >>
  gvs[dft_open_materialize_result_def, dft_open_materialize_def,
      unit_result_rel_def, observable_equiv_def]
QED

(* Abort observations retain the code, not the state or reading counter. *)
Theorem dft_materialized_mixed_terminal_dead_result_rel:
  ((?s. rr = Halt s) \/ (?a s. rr = Abort a s)) /\
  (rr' = rr \/ (?a s t. rr = Abort a s /\ rr' = Abort a t)) ==>
  dead_result_rel D (dft_open_materialize_result xs n rr)
                    (dft_open_materialize_result ys m rr')
Proof
  strip_tac >> gvs[]
  >- metis_tac[dft_materialized_terminal_dead_result_rel]
  >- metis_tac[dft_materialized_terminal_dead_result_rel] >>
  simp[dft_open_materialize_result_def, dead_result_rel_def]
QED
