Theory dftPositionalRoot
Ancestors
  dftPositionalPhase dftPositionalRuntime dftOriginalRuntime
  dftRecursiveOrbitReadiness dftOriginalCutLifecycle dftOriginalScheduleRuntime
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomWf
  relation list

Theorem dft_pos_original_entry_roots:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_original_label_ready C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] nL)) /\
  dft_pos_phase C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] nL))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] nR))
Proof
  strip_tac >>
  `dft_original_function (EL j Corig.ctx_functions) (EL j C.ctx_functions) /\
   dft_original_function (EL j Corig.ctx_functions) (EL j D.ctx_functions)` by
    (fs[dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `fn_entry_label (EL j Corig.ctx_functions) = SOME s.vs_current_bb /\
   fn_entry_label (EL j D.ctx_functions) = SOME s.vs_current_bb` by
    metis_tac[dft_original_function_entry] >>
  `fn_reachable (EL j Corig.ctx_functions) s.vs_current_bb` by
    (simp[fn_reachable_def] >> metis_tac[RTC_REFL]) >>
  `strict_dom_vars_defined (EL j Corig.ctx_functions) s` by
    metis_tac[dft_original_root_dom] >>
  conj_tac
  >- (irule dft_original_label_entry_root >> simp[EL_MEM] >> metis_tac[]) >>
  `dft_original_ready
     (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] nL)) /\
   dft_original_ready
     (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] nR))` by
    metis_tac[dft_original_runtime_root] >>
  `dft_pos_functions C D (EL j C.ctx_functions) (EL j D.ctx_functions)` by
    (simp[dft_pos_functions_def] >> qexists `j` >> simp[]) >>
  irule dft_pos_phase_root >> fs[dft_occ_init_def]
QED
