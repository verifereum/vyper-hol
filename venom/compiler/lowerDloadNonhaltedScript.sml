Theory lowerDloadNonhalted
Ancestors
  lowerDloadOwnership o1LowerDloadRunnerBoundary o1LowerDloadSourceEntry
  o1LowerDloadJointRestore venomExecSemantics venomState list

Theorem ld_annotated_nonhalted_states:
  !vs0 C astk k L AP AG tn fn i s.
    ld_annotated_reachable vs0 C astk k L AP AG tn fn i s ==>
    (~vs0.vs_halted ==> ~s.vs_halted /\
       EVERY (\f. ~f.lf_state.vs_halted) astk)
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac >>
  rpt strip_tac >>
  imp_res_tac ld_step_ok_halted >>
  imp_res_tac ld_enters_block_halted >> gvs[]
  >- metis_tac[ld_setup_callee_not_halted] >>
  `s'.vs_halted = f.lf_state.vs_halted` by
    (drule ld_bind_outputs_vars_only >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms, merge_callee_state_def]) >> gvs[]
QED

Theorem ld_annotated_not_halted:
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ~vs0.vs_halted ==> ~s.vs_halted
Proof
  metis_tac[ld_annotated_nonhalted_states]
QED
