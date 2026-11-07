Theory frameScopedPhaseSimulation
Ancestors frameScopedPhaseCertificates framePhaseCertificates frameIndexedComposition
          frameIndexedCertificates frameFiniteExecution

(* Separate induction outputs are essential: a function run can forget the
   origin of a completed block, but instruction/block splicing cannot. *)
Theorem scoped_phase_finite_induction:
  (!C i s r. finite_step C i s r ==>
    !C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink (g:'g) j t.
    scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink /\
    indexed_entry A R g s t /\ InstPair g i j ==>
    ?h r'. finite_step C' j t r' /\ Q g h r r') /\
  (!C bb s r. finite_block C bb s r ==>
    !C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink (g:'g) bb' t.
    scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink /\
    indexed_entry A R g s t /\ BlockPair bb bb' ==>
    ?h r'. finite_block C' bb' t r' /\ Q g h r r') /\
  (!C fn s r. finite_run C fn s r ==>
    !C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink (g:'g) fn' t.
    scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink /\
    Run g fn fn' s t ==>
    ?h r'. finite_run C' fn' t r' /\ U g h r r')
Proof
  ho_match_mp_tac finite_step_strongind >> rpt conj_tac
  >- suspend "base"
  >- suspend "invoke_return"
  >- suspend "invoke_exit"
  >- suspend "block_term"
  >- suspend "block_next"
  >- suspend "block_exit"
  >- suspend "run_next"
  >- suspend "run_halt"
  >> suspend "run_exit"
QED

Resume scoped_phase_finite_induction[base]:
  rpt strip_tac >> fs[scoped_phase_contract_def] >>
  qpat_x_assum `indexed_base _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_base_def] >> disch_then drule_all >> strip_tac >>
  qexistsl_tac [`h`, `r'`] >> simp[] >>
  irule finite_step_base >> simp[] >>
  qpat_x_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[]
QED

Resume scoped_phase_finite_induction[invoke_return]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_push _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_push_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape U` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all scoped_phase_pop_elim >> strip_tac >>
  qexistsl_tac [`h'`, `OK out'`] >> simp[] >>
  irule finite_step_invoke_return >> metis_tac[]
QED

Resume scoped_phase_finite_induction[invoke_exit]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_push _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_push_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape U` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule scoped_phase_call_exit_elim >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_invoke_exit >> simp[] >> metis_tac[]
QED

Resume scoped_phase_finite_induction[block_term]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_halted_elim >> strip_tac >>
  rename1 `Q g h (OK post) (OK target)` >>
  qexistsl_tac [`h`, `if target.vs_halted then Halt target else OK target`] >>
  conj_tac >- (irule finite_step_block_term >> metis_tac[]) >>
  Cases_on `post.vs_halted` >> fs[] >> metis_tac[indexed_halt_elim]
QED

Resume scoped_phase_finite_induction[block_next]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  qpat_assum `indexed_ok_exit _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_ok_exit_def] >> disch_then drule >> strip_tac >>
  drule_all indexed_increment_elim >> strip_tac >>
  drule_all indexed_admin_entry_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all indexed_splice_elim >> strip_tac >>
  qexistsl_tac [`h'`, `r'`] >> simp[] >>
  irule finite_step_block_next >> metis_tac[]
QED

Resume scoped_phase_finite_induction[block_exit]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >>
  irule finite_step_block_exit >> simp[] >> metis_tac[]
QED

Resume scoped_phase_finite_induction[run_next]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  drule_all scoped_phase_phi_witness >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  `Run h' fn fn' s' t'` by
    (qpat_x_assum `scoped_phase_block_return _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[scoped_phase_block_return_def] >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `!C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink g fn' t. _`
    drule_all >> strip_tac >>
  drule_all indexed_halted_elim >> strip_tac >>
  qpat_x_assum `scoped_phase_run_next _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_run_next_def] >>
  disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_run_next >> metis_tac[]
QED

Resume scoped_phase_finite_induction[run_halt]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  drule_all scoped_phase_phi_witness >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_halted_elim >> strip_tac >>
  qpat_x_assum `scoped_phase_run_halt _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_run_halt_def] >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`h'`, `Halt t'`] >> simp[] >>
  irule finite_step_run_halt >> metis_tac[]
QED

Resume scoped_phase_finite_induction[run_exit]:
  rpt strip_tac >>
  qpat_assum `scoped_phase_contract _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_contract_def] >> strip_tac >>
  drule_all scoped_phase_phi_witness >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape Q` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  qpat_x_assum `scoped_phase_run_exit _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_phase_run_exit_def] >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_run_exit >> simp[] >> metis_tac[]
QED
Finalise scoped_phase_finite_induction

Theorem scoped_phase_finite_simulation:
  scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink ==>
  scoped_phase_simulates C C' A R Run BlockPair InstPair Q U
Proof
  simp[scoped_phase_simulates_def] >> metis_tac[scoped_phase_finite_induction]
QED

Theorem scoped_phase_run_simulation:
  scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink /\
  Run (g:'g) fn fn' s t /\ (!e. run_blocks n C fn s <> Error e) ==>
  ?m (h:'g) r'. run_blocks m C' fn' t = r' /\ U g h (run_blocks n C fn s) r'
Proof
  rpt strip_tac >>
  `finite_run C fn s (run_blocks n C fn s)` by metis_tac[finite_run_iff] >>
  drule (cj 3 scoped_phase_finite_induction) >>
  disch_then drule >> disch_then drule >> strip_tac >>
  fs[finite_run_iff] >> metis_tac[]
QED

val _ = export_theory();
