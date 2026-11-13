(* Cross bytes are needed only through the selected invocation's return.
   The complete source history and translation maps are retained separately. *)
Theory readonlyInvokeCopyFwdLiveCertificates
Ancestors
  readonlyInvokeCopyFwdProtectionLifetime readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdProtectionRetirement readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistoryStackAlignment
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim venomInstProofs
  venomExecSemantics list rich_list pred_set arithmetic

Definition ricf_live_ledger_def:
  ricf_live_ledger s ledger =
    FILTER (\entry. ricf_active_use (FST entry) (SND entry) s) ledger
End

Theorem ricf_live_ledger_empty[simp]:
  ricf_live_ledger s [] = []
Proof
  simp[ricf_live_ledger_def]
QED

Theorem ricf_live_ledger_member:
  MEM (p,pre) (ricf_live_ledger s ledger) <=>
  MEM (p,pre) ledger /\ ricf_active_use p pre s
Proof
  simp[ricf_live_ledger_def, MEM_FILTER, CONJ_COMM]
QED

Theorem ricf_live_ledger_subset:
  set (ricf_live_ledger s ledger) SUBSET set ledger
Proof
  simp[ricf_live_ledger_def, SUBSET_DEF, MEM_FILTER]
QED

Theorem ricf_live_ledger_idempotent:
  ricf_live_ledger s (ricf_live_ledger s ledger) = ricf_live_ledger s ledger
Proof
  simp[ricf_live_ledger_def, FILTER_FILTER, combinTheory.o_DEF]
QED

Theorem ricf_live_ledger_retire:
  MEM (p,pre) ledger /\ ~ricf_active_use p pre s ==>
  ~MEM (p,pre) (ricf_live_ledger s ledger)
Proof
  simp[ricf_live_ledger_member]
QED

Theorem ricf_live_phase_ranges:
  ricf_phase_ranges depth (ricf_live_ledger s ledger) SUBSET
  ricf_phase_ranges depth ledger
Proof
  simp[ricf_phase_ranges_def, SUBSET_DEF, ricf_live_ledger_member] >> metis_tac[]
QED

Theorem ricf_live_cross_retire:
  ircf_cross tn (ricf_phase_ranges depth ledger) s t ==>
  ircf_cross tn (ricf_phase_ranges depth (ricf_live_ledger u ledger)) s t
Proof
  metis_tac[ircf_cross_subset, ricf_live_phase_ranges]
QED

Theorem ricf_live_cert_crosses_retire:
  ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t ==>
  ricf_cert_crosses tn
    (ricf_phase_stack_ranges stk (ricf_live_ledger u ledger)) stk s t
Proof
  strip_tac >> irule ricf_cert_crosses_subset >>
  qexists_tac `ricf_phase_stack_ranges stk ledger` >>
  simp[ricf_phase_stack_ranges_def, ricf_live_phase_ranges]
QED

Theorem ricf_active_use_later:
  t.vs_current_bb = s.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx /\
  ricf_active_use p pre t ==>
  ricf_active_use p pre s
Proof
  Cases_on `pre = []`
  >- (simp[ricf_active_use_owner, ricf_remaining_selected_use_def] >>
      metis_tac[LESS_EQ_TRANS]) >>
  simp[ricf_active_use_def, ricf_visit_owner_state_def]
QED

Theorem ricf_live_ledger_later:
  t.vs_current_bb = s.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx ==>
  set (ricf_live_ledger t ledger) SUBSET set (ricf_live_ledger s ledger)
Proof
  simp[SUBSET_DEF, ricf_live_ledger_def, MEM_FILTER] >>
  rpt strip_tac >> Cases_on `x` >> gvs[] >> metis_tac[ricf_active_use_later]
QED

Theorem ricf_live_ledger_next:
  step_inst fuel C inst s = OK u /\ ~is_terminator inst.inst_opcode ==>
  set (ricf_live_ledger (u with vs_inst_idx := SUC s.vs_inst_idx) ledger)
    SUBSET set (ricf_live_ledger s ledger)
Proof
  strip_tac >> drule_all step_preserves_control_flow >> strip_tac >>
  irule ricf_live_ledger_later >> simp[]
QED

(* Every future selected use retains its certificate. Already retired entries
   in the complete history cannot be inserted by this relation. *)
Definition ricf_certificate_coverage_def:
  ricf_certificate_coverage s history certificates <=>
    set certificates SUBSET set history /\
    !p pre. MEM (p,pre) history /\
      ricf_remaining_selected_use p (ricf_visit_owner_state pre s) ==>
      MEM (p,pre) certificates
End

Theorem ricf_certificate_coverage_empty[simp]:
  ricf_certificate_coverage s [] []
Proof
  simp[ricf_certificate_coverage_def]
QED

Theorem ricf_certificate_coverage_filter:
  ricf_certificate_coverage s history certificates ==>
  ricf_certificate_coverage s history (ricf_live_ledger s certificates)
Proof
  rw[ricf_certificate_coverage_def]
  >- metis_tac[SUBSET_TRANS, ricf_live_ledger_subset] >>
  simp[ricf_live_ledger_member, ricf_active_use_def]
QED

Theorem ricf_remaining_selected_later:
  t.vs_current_bb = s.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx /\
  ricf_remaining_selected_use p (ricf_visit_owner_state pre t) ==>
  ricf_remaining_selected_use p (ricf_visit_owner_state pre s)
Proof
  Cases_on `pre = []` >> simp[ricf_visit_owner_state_def]
  >- (simp[ricf_remaining_selected_use_def] >> metis_tac[LESS_EQ_TRANS])
QED

Theorem ricf_certificate_coverage_advance:
  ricf_certificate_coverage s history certificates /\
  t.vs_current_bb = s.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx ==>
  ricf_certificate_coverage t history certificates
Proof
  simp[ricf_certificate_coverage_def] >> metis_tac[ricf_remaining_selected_later]
QED

Theorem ricf_certificate_coverage_later:
  ricf_certificate_coverage s history certificates /\
  t.vs_current_bb = s.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx ==>
  ricf_certificate_coverage t history (ricf_live_ledger t certificates)
Proof
  metis_tac[ricf_certificate_coverage_advance, ricf_certificate_coverage_filter]
QED

Theorem ricf_certificate_coverage_next:
  ricf_certificate_coverage s history certificates /\
  step_inst fuel C inst s = OK u /\ ~is_terminator inst.inst_opcode ==>
  ricf_certificate_coverage (u with vs_inst_idx := SUC s.vs_inst_idx)
    history (ricf_live_ledger (u with vs_inst_idx := SUC s.vs_inst_idx) certificates)
Proof
  strip_tac >> drule_all step_preserves_control_flow >> strip_tac >>
  irule ricf_certificate_coverage_later >> qexists_tac `s` >> simp[]
QED

Theorem ricf_visit_owner_state_push:
  f.cf_state = s ==>
  ricf_visit_owner_state (f::pre) t = ricf_visit_owner_state pre s
Proof
  Cases_on `pre` >> simp[ricf_visit_owner_state_def]
QED

Theorem ricf_certificate_coverage_push:
  ricf_certificate_coverage s history certificates /\ f.cf_state = s ==>
  ricf_certificate_coverage t (ricf_phase_push f history)
    (ricf_phase_push f certificates)
Proof
  simp[ricf_certificate_coverage_def, ricf_phase_push_def,
    SUBSET_DEF, MEM_MAP] >> rpt strip_tac
  >- (rename1 `MEM entry certificates` >> Cases_on `entry` >> gvs[] >>
      rename1 `MEM (p,pre) certificates` >> qexists_tac `(p,pre)` >> simp[]) >>
  rename1 `MEM entry history` >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,pre) history` >> qexists_tac `(p,pre)` >> simp[] >>
  metis_tac[ricf_visit_owner_state_push]
QED

Theorem ricf_certificate_coverage_inherited:
  ricf_certificate_coverage s history certificates ==>
  ricf_certificate_coverage t
    (FILTER (\entry. SND entry <> []) history)
    (FILTER (\entry. SND entry <> []) certificates)
Proof
  simp[ricf_certificate_coverage_def, SUBSET_DEF, MEM_FILTER] >>
  rpt strip_tac >>
  `ricf_visit_owner_state pre t = ricf_visit_owner_state pre s` by
    simp[ricf_visit_owner_state_def] >> metis_tac[]
QED

Theorem ricf_visit_owner_state_pop_later[local]:
  pre <> [] /\ HD pre = f /\
  t.vs_current_bb = f.cf_state.vs_current_bb /\
  f.cf_state.vs_inst_idx <= t.vs_inst_idx /\
  ricf_remaining_selected_use p (ricf_visit_owner_state (TL pre) t) ==>
  ricf_remaining_selected_use p (ricf_visit_owner_state pre u)
Proof
  Cases_on `pre` >> simp[] >> qmatch_goalsub_rename_tac `ricf_visit_owner_state rest t` >>
  Cases_on `rest` >>
  simp[ricf_visit_owner_state_def, ricf_remaining_selected_use_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem ricf_certificate_coverage_pop:
  ricf_certificate_coverage s history certificates /\
  (!p pre. MEM (p,pre) history /\ pre <> [] ==> HD pre = f) /\
  t.vs_current_bb = f.cf_state.vs_current_bb /\
  f.cf_state.vs_inst_idx <= t.vs_inst_idx ==>
  ricf_certificate_coverage t (ricf_phase_pop history)
    (ricf_live_ledger t (ricf_phase_pop certificates))
Proof
  strip_tac >> irule ricf_certificate_coverage_filter >>
  fs[ricf_certificate_coverage_def, SUBSET_DEF] >>
  simp[ricf_certificate_coverage_def, SUBSET_DEF, ricf_phase_pop_def,
    MEM_MAP, MEM_FILTER] >> rpt strip_tac
  >- (rename1 `MEM entry certificates` >> Cases_on `entry` >> gvs[] >>
      rename1 `MEM (p,pre) certificates` >> qexists_tac `(p,pre)` >> simp[]) >>
  rename1 `MEM entry history` >> Cases_on `entry` >> gvs[] >>
  rename1 `MEM (p,pre) history` >>
  qexists_tac `(p,pre)` >> simp[] >>
  `ricf_remaining_selected_use p (ricf_visit_owner_state pre s)` by
    (irule ricf_visit_owner_state_pop_later >> metis_tac[]) >> metis_tac[]
QED
