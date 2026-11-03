(* Change the callee context without changing the executing frame. *)
Theory dftFrameContext
Ancestors
  dftRunRel o1PassLift venomExecSemantics venomState venomInst
  contextCodegenRel ctxLookupAgreeHelpers venomExecProps list option

Theorem dft_setup_callee_same[local]:
  dft_fn_rel f g ==> setup_callee f args s = setup_callee g args s
Proof
  strip_tac >> drule dft_fn_rel_entry_label >>
  Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def, setup_callee_def]
QED

Theorem dft_returning_run_context[local]:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  ctx_labels_bound C s.vs_labels /\
  lookup_function nm C.ctx_functions = SOME f /\
  lookup_function nm C'.ctx_functions = SOME g /\
  fn_entry_label f = SOME s.vs_current_bb /\
  run_blocks fuel C' g s = IntRet ret t ==>
  run_blocks fuel C f s = IntRet ret t
Proof
  strip_tac >> drule_all dft_run_blocks_rel >>
  disch_then (qspec_then `fuel` mp_tac) >>
  Cases_on `run_blocks fuel C f s` >> simp[dft_res_rel_def]
QED

Theorem dft_step_context:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  ctx_labels_bound C s.vs_labels /\ step_inst fuel C' i s = OK t ==>
  step_inst fuel C i s = OK t
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule dft_fn_rel_lookup_function >>
      disch_then (qspec_then `callee_name` mp_tac) >>
      Cases_on `lookup_function callee_name C.ctx_functions` >>
      simp[OPTREL_def] >> strip_tac >>
      rename1 `dft_fn_rel f callee_fn` >>
      `setup_callee f args s = SOME callee_s`
        by metis_tac[dft_setup_callee_same] >>
      `fn_entry_label f = SOME callee_s.vs_current_bb`
        by metis_tac[setup_callee_fn_entry_state, fn_entry_state_def] >>
      `callee_s.vs_labels = s.vs_labels` by gvs[setup_callee_def, AllCaseEqs()] >>
      `run_blocks fuel C f callee_s = IntRet ret callee_s'`
        by (irule dft_returning_run_context >> metis_tac[]) >>
      simp[Once step_inst_def]) >>
  gvs[step_inst_non_invoke]
QED

Theorem dft_enters_block_labels[local]:
  enters_block fn s t ==> t.vs_labels = s.vs_labels
Proof
  rw[enters_block_def] >> drule eval_phis_preserves_labels >> simp[]
QED

Theorem dft_frame_reach_labels:
  !C fn s0 i s. frame_reach C fn s0 i s ==> s.vs_labels = s0.vs_labels
Proof
  ho_match_mp_tac frame_reach_ind >> rpt strip_tac >>
  imp_res_tac dft_enters_block_labels >>
  imp_res_tac step_inst_preserves_labels_always >> simp[]
QED

Theorem dft_frame_reach_context:
  !C' fn s0 i s. frame_reach C' fn s0 i s ==>
  !C. LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
      ctx_labels_bound C s0.vs_labels ==> frame_reach C fn s0 i s
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac >> rpt strip_tac
  >- (irule (cj 1 frame_reach_rules) >> metis_tac[])
  >- (irule (cj 2 frame_reach_rules) >>
      imp_res_tac dft_frame_reach_labels >>
      `ctx_labels_bound C s.vs_labels` by metis_tac[] >>
      drule_all dft_step_context >> strip_tac >> metis_tac[]) >>
  irule (cj 3 frame_reach_rules) >>
  imp_res_tac dft_frame_reach_labels >>
      `ctx_labels_bound C s.vs_labels` by metis_tac[] >>
  drule_all dft_step_context >> strip_tac >> metis_tac[]
QED
