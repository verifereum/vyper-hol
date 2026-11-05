Theory dftPositionalClosure
Ancestors
  dftPositionalLifecycle dftPositionalStep dftPositionalReturn
  dftPositionalPhase dftPositionalRuntime dftOccurrenceReplay
  dftOccurrenceMachine dftOpenMachine venomInst venomState list arithmetic

Theorem dft_pos_rooted_progress:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR l r ==>
  ?a b. 0 < a /\ a <= 2 /\ 0 < b /\ b <= 2 /\
    dft_pos_rooted_phase w C D fi bi pre x call post
      (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r)
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >>
  disch_then (assume_tac o CONJUNCT1) >>
  qpat_assum `dft_pos_phase _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_pos_phase_def] >> strip_tac >>
  qpat_x_assum `dft_pos_control _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_pos_control_def] >> strip_tac
  >- suspend "enter"
  >- suspend "at"
  >> suspend "done"
QED

Resume dft_pos_rooted_progress[enter]:
  fs[] >>
  `dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)` by
    (irule dft_pos_enter_next >> metis_tac[]) >>
  qexistsl_tac [`1`, `1`] >> simp[] >>
  metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1]
QED

Resume dft_pos_rooted_progress[at]:
  fs[] >> Cases_on `j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre`
  >- (fs[] >> drule_all dft_pos_root_crossing_next >> strip_tac >>
      qexistsl_tac [`2`, `1`] >> simp[] >> metis_tac[]) >>
  `dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)` by
    (irule dft_pos_at_outside_next >> goal_assum drule >> metis_tac[]) >>
  qexistsl_tac [`1`, `1`] >> simp[] >>
  metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1]
QED

Resume dft_pos_rooted_progress[done]:
  fs[] >> drule_all dft_pos_done_next >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qexistsl_tac [`1`, `b`] >>
  `0 < b /\ b <= 2` by decide_tac >> simp[] >>
  metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1]
QED
Finalise dft_pos_rooted_progress

Theorem dft_pos_rooted_cofinal:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR l r ==>
  !N M. ?a b. N <= a /\ M <= b /\
    dft_pos_rooted_phase w C D fi bi pre x call post
      (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r)
Proof
  strip_tac >>
  `!k. ?a b. k <= a /\ k <= b /\
    dft_pos_rooted_phase w C D fi bi pre x call post
      (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r)` by
    (Induct
     >- (qexistsl_tac [`0`, `0`] >> simp[] >> metis_tac[]) >>
     pop_assum (qx_choosel_then [`a`, `b`] strip_assume_tac) >>
     drule_all dft_pos_rooted_progress >>
     disch_then (qx_choosel_then [`da`, `db`] strip_assume_tac) >>
     qexistsl_tac [`da + a`, `db + b`] >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     fs[FUNPOW_ADD] >> metis_tac[]) >>
  rpt gen_tac >> first_x_assum (qspec_then `MAX N M` strip_assume_tac) >>
  qexistsl_tac [`a`, `b`] >> Cases_on `N <= M` >> fs[MAX_DEF] >> decide_tac
QED
