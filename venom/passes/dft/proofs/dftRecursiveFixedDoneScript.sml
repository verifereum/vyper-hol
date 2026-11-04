Theory dftRecursiveFixedDone
Ancestors
  dftRecursiveFixedStep dftRecursiveFixedPhase dftRecursiveReturnPhase
  dftRecursiveCallProvenance dftRecursiveCallResidual dftOccurrenceReturn
  dftOccurrenceSuspended dftOccurrenceReplay dftOccurrenceMachine
  dftOpenMachine dftOpenErase dftOriginalRuntime venomExecSemantics
  venomState list arithmetic

Theorem dft_fixed_done_intro[local]:
  c.dft_occ_core = DftOpen (DftDone res) ls nL /\
  d.dft_occ_core = DftOpen (DftDone res) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_fixed_phase q pre x call post c d
Proof
  strip_tac >> simp[dft_fixed_phase_def] >>
  qexists `certs` >> simp[dft_fixed_control_def] >> metis_tac[]
QED

Theorem dft_fixed_done_inversion:
  dft_fixed_phase q pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone res) ls n ==>
  ?certs rs nR.
    d.dft_occ_core = DftOpen (DftDone res) rs nR /\
    dft_fixed_stack q pre x call post certs ls rs /\
    c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
    c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
    dft_original_ready c /\ dft_original_ready d
Proof
  simp[dft_fixed_phase_def] >> strip_tac >>
  gvs[dft_fixed_control_def] >> metis_tac[]
QED

Theorem dft_fixed_done_terminal_next[local]:
  c.dft_occ_core = DftOpen (DftDone res) ls n /\
  (ls = [] \/ (!ret cs. res <> IntRet ret cs)) ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone res) [] n; dft_occ_saved := []|>
Proof
  strip_tac >> Cases_on `res` >> Cases_on `ls` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
      dft_fill_def, dft_fill_control_def, dft_open_next_def,
      dft_open_return_def, dft_erase_def, dft_occ_update_def]
QED

Theorem dft_fixed_done_terminal:
  dft_fixed_phase q pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone res) ls n /\
  (ls = [] \/ (!ret cs. res <> IntRet ret cs)) /\
  dft_original_context Corig C /\ dft_original_context Dorig D ==>
  dft_fixed_phase q pre x call post
    (dft_occ_oracle_next w C c) (dft_occ_oracle_next w D d)
Proof
  strip_tac >> drule_all dft_fixed_done_inversion >> strip_tac >>
  `rs = [] \/ (!ret cs. res <> IntRet ret cs)` by
    (gvs[dft_fixed_stack_def, LIST_REL_EL_EQN, dft_provenanced_frames_def] >>
     Cases_on `certs` >> gvs[dft_provenanced_frames_def]) >>
  `dft_original_ready (dft_occ_oracle_next w C c) /\
   dft_original_ready (dft_occ_oracle_next w D d)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone res) [] n; dft_occ_saved := []|>` by
    metis_tac[dft_fixed_done_terminal_next] >>
  `dft_occ_oracle_next w D d = d with
    <|dft_occ_core := DftOpen (DftDone res) [] nR; dft_occ_saved := []|>` by
    metis_tac[dft_fixed_done_terminal_next] >>
  irule dft_fixed_done_intro >> simp[] >> qexists `[]` >> simp[]
QED

Theorem dft_fixed_done_ghosts[local]:
  c.dft_occ_core = DftOpen (DftDone res) ls n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftDone out) rs m ==>
  (dft_occ_oracle_next w C c).dft_occ_path = c.dft_occ_path /\
  (dft_occ_oracle_next w C c).dft_occ_visit = c.dft_occ_visit
Proof
  simp[dft_occ_oracle_next_def, dft_occ_next_def] >> strip_tac >>
  Cases_on `rs` >> simp[dft_occ_update_def]
QED

Theorem dft_fixed_done_cleared:
  dft_fixed_phase q pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone res) ls n /\
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftDone out) [] nL /\
  (dft_occ_oracle_next w D d).dft_occ_core = DftOpen (DftDone out) [] nR /\
  (dft_occ_oracle_next w C c).dft_occ_saved = [] /\
  (dft_occ_oracle_next w D d).dft_occ_saved = [] /\
  dft_original_context Corig C /\ dft_original_context Dorig D ==>
  dft_fixed_phase q pre x call post
    (dft_occ_oracle_next w C c) (dft_occ_oracle_next w D d)
Proof
  strip_tac >> drule_all dft_fixed_done_inversion >> strip_tac >>
  `dft_original_ready (dft_occ_oracle_next w C c) /\
   dft_original_ready (dft_occ_oracle_next w D d)` by
    metis_tac[dft_original_runtime_next] >>
  `((dft_occ_oracle_next w C c).dft_occ_path = c.dft_occ_path) /\
   ((dft_occ_oracle_next w C c).dft_occ_visit = c.dft_occ_visit) /\
   ((dft_occ_oracle_next w D d).dft_occ_path = d.dft_occ_path) /\
   ((dft_occ_oracle_next w D d).dft_occ_visit = d.dft_occ_visit)` by
    metis_tac[dft_fixed_done_ghosts] >>
  irule dft_fixed_done_intro >> simp[] >> qexists `[]` >> simp[]
QED

Theorem dft_fixed_plain_done:
  dft_fixed_phase q pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (fl::ls) n /\
  dft_fixed_stack q pre x call post (NONE::certs) (fl::ls) (fr::rs) /\
  d.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (fr::rs) nR /\
  c.dft_occ_saved = (path,visit)::saved /\ d.dft_occ_saved = (path,visit)::saved /\
  LENGTH saved = LENGTH certs /\
  dft_original_context Corig C /\ dft_original_context Dorig D ==>
  dft_fixed_phase q pre x call post
    (dft_occ_oracle_next w C c) (dft_occ_oracle_next w D d)
Proof
  strip_tac >>
  `dft_original_ready c /\ dft_original_ready d` by fs[dft_fixed_phase_def] >>
  `dft_original_ready (dft_occ_oracle_next w C c) /\
   dft_original_ready (dft_occ_oracle_next w D d)` by
    metis_tac[dft_original_runtime_next] >>
  qpat_x_assum `dft_fixed_stack _ _ _ _ _ (NONE::_) _ _` mp_tac >>
  rewrite_tac[dft_fixed_stack_cons] >> strip_tac >>
  Cases_on `fl` >> Cases_on `fr` >>
  gvs[dft_provenanced_frame_def, dft_recursive_frame_def, dft_recursive_payload_def] >>
  rename1 `DftCaller fn 0 bb inst caller` >>
  Cases_on `dft_restore inst.inst_outputs ret cs caller`
  >- (irule dft_fixed_done_cleared >>
      metis_tac[dft_suspend_pop_failure]) >>
  rename1 `dft_restore inst.inst_outputs ret cs caller = SOME after` >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    (fs[dft_fixed_stack_def] >> metis_tac[dft_provenanced_frames_fill]) >>
  `dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftAt fn 0 bb
      (after with vs_inst_idx := SUC caller.vs_inst_idx)) ls n;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    metis_tac[dft_suspend_pop] >>
  `dft_occ_oracle_next w D d = d with
    <|dft_occ_core := DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
      (dft_gas_edit_block q pre x call post bb)
      (after with vs_inst_idx := SUC caller.vs_inst_idx)) rs nR;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    metis_tac[dft_suspend_pop] >>
  irule dft_fixed_at_intro >> simp[] >> qexists `certs` >>
  simp[] >> metis_tac[dft_fixed_plain_resume_safe]
QED

Theorem dft_fixed_pending_done[local]:
  dft_fixed_phase q pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (fl::ls) n /\
  dft_fixed_stack q pre x call post (SOME z::certs) (fl::ls) (fr::rs) /\
  d.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (fr::rs) nR /\
  c.dft_occ_saved = (path,visit)::saved /\ d.dft_occ_saved = (path,visit)::saved /\
  LENGTH saved = LENGTH certs /\
  dft_original_context Corig C /\ dft_original_context Dorig D ==>
  ?k. (k = 1 \/ k = 2) /\
    dft_fixed_phase q pre x call post
      (dft_occ_oracle_next w C c) (FUNPOW (dft_occ_oracle_next w D) k d)
Proof
  strip_tac >>
  `dft_original_ready c /\ dft_original_ready d` by fs[dft_fixed_phase_def] >>
  qpat_x_assum `dft_fixed_stack _ _ _ _ _ (SOME _::_) _ _` mp_tac >>
  rewrite_tac[dft_fixed_stack_cons] >> strip_tac >>
  `dft_fixed_certificate q pre x call post z` by fs[dft_fixed_coordinate_def] >>
  `z.dft_cert_forward` by fs[dft_fixed_certificate_def] >>
  gvs[dft_provenanced_frame_def, dft_certificate_saved_def, LET_THM] >>
  Cases_on `dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start`
  >- (qexists `1` >> simp[FUNPOW_1] >>
      irule dft_fixed_done_cleared >>
      `dft_restore z.dft_cert_call.inst_outputs ret cs
        (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = NONE` by
        metis_tac[dft_restore_pair_failure] >>
      metis_tac[dft_suspend_pop_failure]) >>
  `?a. dft_restore z.dft_cert_call.inst_outputs ret cs
      (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a` by
    (Cases_on `dft_restore z.dft_cert_call.inst_outputs ret cs
      (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)` >>
     metis_tac[dft_restore_pair_failure, optionTheory.NOT_NONE_SOME]) >>
  rename1 `dft_restore _ _ _ z.dft_cert_start = SOME restored` >>
  qexists `2` >> simp[] >> irule dft_fixed_done_reentry >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`a`, `restored`, `certs`, `z`] >> simp[]
QED

Theorem dft_fixed_done_next:
  dft_fixed_phase q pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone res) ls n /\
  dft_original_context Corig C /\ dft_original_context Dorig D ==>
  ?k. (k = 1 \/ k = 2) /\
    dft_fixed_phase q pre x call post
      (dft_occ_oracle_next w C c) (FUNPOW (dft_occ_oracle_next w D) k d)
Proof
  strip_tac >>
  Cases_on `ls = [] \/ (!ret cs. res <> IntRet ret cs)`
  >- (qexists `1` >> simp[FUNPOW_1] >>
      metis_tac[dft_fixed_done_terminal]) >>
  gvs[] >>
  drule_all dft_fixed_done_inversion >> strip_tac >>
  Cases_on `ls` >- gvs[] >>
  Cases_on `certs`
  >- gvs[dft_fixed_stack_def, dft_provenanced_frames_def] >>
  Cases_on `rs`
  >- gvs[dft_fixed_stack_def, dft_provenanced_frames_def] >>
  Cases_on `c.dft_occ_saved` >- gvs[] >>
  rename1 `c.dft_occ_saved = pv::saved` >> PairCases_on `pv` >>
  gvs[] >>
  rename1 `dft_fixed_stack q pre x call post (annotation::rest) _ _` >>
  Cases_on `annotation`
  >- (qexists `1` >> simp[FUNPOW_1] >>
      irule dft_fixed_plain_done >> metis_tac[]) >>
  irule dft_fixed_pending_done >> metis_tac[]
QED
