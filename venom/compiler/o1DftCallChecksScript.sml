(*
 * dft_fn keeps every external call's success flag checked
 * (call_checks_ok) on an SSA function.  dftCallChecks proves it for one
 * rescheduling of each block (dft_blocks_call_checks_ok); dft_fn's
 * worklist loop reschedules one block at a time, possibly a block more
 * than once.  Off SSA it fails: a redefinition of the flag can be
 * scheduled between the call and its check.
 *)
Theory o1DftCallChecks
Ancestors
  dftCallChecks unitShapeDefs dftDefs venomWf dftLifting
  dftScheduleOrder dftSsaPreserve dftCorrectness list venomInst unitLabelMapIdentity

Theorem o1_dft_blocks_inst_wf[local]:
  LIST_REL dftLifting$dft_block_rel fn.fn_blocks bbs ==>
  fn_inst_wf (fn with fn_blocks := bbs)
Proof
  strip_tac >> simp[fn_inst_wf_def] >> rpt strip_tac >>
  drule_all dftLiftingTheory.dft_blocks_rel_source >> strip_tac >>
  gvs[dftLiftingTheory.dft_block_rel_def, EVERY_MEM]
QED

Theorem o1_dft_blocks_wf_function[local]:
  wf_function fn /\
  LIST_REL dftLifting$dft_block_rel fn.fn_blocks bbs ==>
  wf_function (fn with fn_blocks := bbs)
Proof
  strip_tac >> drule dftLiftingTheory.dft_block_rel_labels >> strip_tac >>
  simp[wf_function_def] >> rpt conj_tac
  >~ [`ALL_DISTINCT _`] >- gvs[wf_function_def, fn_labels_def]
  >~ [`fn_has_entry _`] >- (gvs[fn_has_entry_def, wf_function_def] >>
                               metis_tac[MAP_EQ_NIL])
  >~ [`!bb. MEM bb _ ==> bb_well_formed bb`]
  >- (rpt strip_tac >>
      drule_all dftLiftingTheory.dft_blocks_rel_source >> strip_tac >>
      gvs[dftLiftingTheory.dft_block_rel_def])
  >~ [`fn_inst_ids_distinct _`]
  >- (simp[fn_inst_ids_distinct_def] >>
      irule dftLiftingTheory.dft_blocks_rel_distinct_ids >>
      qexists_tac `fn.fn_blocks` >>
      gvs[wf_function_def, fn_inst_ids_distinct_def]) >>
  simp[fn_succs_closed_def] >> rpt strip_tac >>
  drule_all dftLiftingTheory.dft_blocks_rel_source >> strip_tac >>
  `bb_succs bb = bb_succs a` by
    (irule dftLiftingTheory.dft_block_rel_succs >>
     gvs[wf_function_def] >> metis_tac[]) >>
  gvs[wf_function_def, fn_succs_closed_def, fn_labels_def] >> metis_tac[]
QED

Theorem o1_dft_process_one_schedule[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) st.dls_blocks) ==>
  LIST_REL (\bb bb'. bb' = bb \/ ?order. bb' = dft_block order bb)
    st.dls_blocks (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[]
  >- simp[LIST_REL_EL_EQN] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- simp[LIST_REL_EL_EQN] >>
  simp[LIST_REL_MAP2, LIST_REL_EL_EQN] >>
  qx_gen_tac `n` >> strip_tac >>
  qmatch_goalsub_abbrev_tac `b.bb_label` >>
  `MEM b st.dls_blocks` by simp[Abbr `b`, EL_MEM] >>
  Cases_on `b.bb_label = lbl` >> simp[] >>
  `lookup_block lbl st.dls_blocks = SOME b` by
    (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Definition o1_dft_checks_inv_def:
  o1_dft_checks_inv fn bbs <=>
    LIST_REL dftLifting$dft_block_rel fn.fn_blocks bbs /\
    LIST_REL dftScheduleOrder$dft_block_rel fn.fn_blocks bbs /\
    dft_inv bbs /\ call_checks_ok (fn with fn_blocks := bbs)
End

Theorem o1_dft_process_one_checks[local]:
  wf_function fn /\ ssa_form fn /\ o1_dft_checks_inv fn st.dls_blocks ==>
  call_checks_ok
    (fn with fn_blocks := (FST (dft_process_one cfg lr fn st lbl)).dls_blocks)
Proof
  simp[o1_dft_checks_inv_def] >> strip_tac >>
  `wf_function (fn with fn_blocks := st.dls_blocks)` by
    (irule o1_dft_blocks_wf_function >> simp[]) >>
  `fn_inst_wf (fn with fn_blocks := st.dls_blocks)` by
    (irule o1_dft_blocks_inst_wf >> simp[]) >>
  `ssa_form (fn with fn_blocks := st.dls_blocks)` by
    (irule dftSsaPreserveTheory.dft_block_rel_ssa_form >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) st.dls_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  drule o1_dft_process_one_schedule >>
  disch_then (qspecl_then [`lr`, `lbl`, `fn`, `cfg`] assume_tac) >>
  drule_at (Pos hd) dft_blocks_call_checks_ok >>
  disch_then (qspec_then
    `(FST (dft_process_one cfg lr fn st lbl)).dls_blocks` mp_tac) >>
  simp[] >> impl_tac
  >- (gvs[dft_inv_def, EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

Theorem o1_dft_loop_step_checks[local]:
  wf_function fn /\ ssa_form fn /\
  o1_dft_checks_inv fn (FST trip).dls_blocks ==>
  o1_dft_checks_inv fn (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `LIST_REL dftLifting$dft_block_rel fn.fn_blocks (FST trip).dls_blocks` by
    gvs[o1_dft_checks_inv_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) (FST trip).dls_blocks)` by
    metis_tac[dftLiftingTheory.dft_block_rel_labels] >>
  simp[o1_dft_checks_inv_def] >> conj_tac
  >- (irule dftLiftingTheory.dft_loop_step_block_rel >> simp[]) >>
  conj_tac
  >- (irule dftScheduleOrderTheory.dft_loop_step_block_rel >>
      gvs[o1_dft_checks_inv_def] >>
      simp[EVERY_MEM] >> metis_tac[bb_inst_ids_distinct]) >>
  conj_tac
  >- (irule dft_loop_step_preserves_inv >> gvs[o1_dft_checks_inv_def]) >>
  `call_checks_ok (fn with fn_blocks := (FST trip).dls_blocks)` by
    gvs[o1_dft_checks_inv_def] >>
  PairCases_on `trip` >> gvs[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> Cases_on `trip1` >> simp[] >>
  drule_all o1_dft_process_one_checks >>
  disch_then (qspecl_then [`lr`, `h`, `cfg`] mp_tac) >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> gvs[]
QED

Theorem o1_funpow_dft_checks[local]:
  !n trip. wf_function fn /\ ssa_form fn /\
    o1_dft_checks_inv fn (FST trip).dls_blocks ==>
    o1_dft_checks_inv fn
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_SUC] >> rpt strip_tac >>
  irule o1_dft_loop_step_checks >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem dft_fn_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ fn_pseudos_prefix fn /\
  EVERY inst_shape_ok (fn_insts fn) /\ call_checks_ok fn ==>
  call_checks_ok (dft_fn fn)
Proof
  strip_tac >>
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `o1_dft_checks_inv fn fn.fn_blocks` by
    (simp[o1_dft_checks_inv_def] >> rpt conj_tac
     >- (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
         irule dftLiftingTheory.dft_block_rel_refl >>
         fs[wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >>
         metis_tac[EL_MEM, bb_inst_ids_distinct, wf_function_def])
     >- (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
         irule dftScheduleOrderTheory.dft_block_rel_refl >>
         gvs[fn_pseudos_prefix_def, EVERY_MEM] >>
         metis_tac[EL_MEM, bb_inst_ids_distinct, wf_function_def]) >>
     metis_tac[wf_fn_initial_dft_inv]) >>
  simp[dft_fn_def, LET_THM] >> pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `FUNPOW dstep fuel initial` >>
  `o1_dft_checks_inv fn (FST (FUNPOW dstep fuel initial)).dls_blocks` by
    (simp[NoAsms, Abbr `dstep`] >> irule o1_funpow_dft_checks >>
     simp[Abbr `initial`]) >>
  gvs[o1_dft_checks_inv_def]
QED
