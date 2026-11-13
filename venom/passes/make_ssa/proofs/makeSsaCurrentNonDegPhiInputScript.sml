Theory makeSsaCurrentNonDegPhiInput
Ancestors
  makeSsaCurrentNonDegShape makeSsaCurrentSourceCuts
  makeSsaCurrentNonDegCleanup makeSsaDefs venomInst

Theorem current_nondeg_phi_input:
  wf_function fn /\ fn_inst_wf fn /\
  blocks_have_leading_phi fn.fn_blocks /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_phis_non_degenerate fn'
Proof
  strip_tac >>
  `?eb. entry_block fn = SOME eb` by
    (Cases_on `fn.fn_blocks` >>
     gvs[entry_block_def, blocks_have_leading_phi_def]) >>
  drule_all current_make_ssa_stages >> strip_tac >>
  `EVERY current_nondeg_block_shape fn.fn_blocks` by
    metis_tac[current_nondeg_input_shape] >>
  drule_all current_nondeg_add_placement_shape >> strip_tac >>
  drule_all (CONJUNCT1 current_nondeg_rename_shape) >> strip_tac >>
  gvs[] >>
  qspec_then `fn with fn_blocks := renamed` mp_tac
    (GEN_ALL current_nondeg_clean_function) >>
  simp[]
QED
