Theory framePhaseSimulation
Ancestors framePhaseCertificates frameIndexedComposition frameIndexedCertificates
          frameFiniteExecution

Definition phase_contract_def:
  phase_contract C C' A R Run BlockPair InstPair Q PushRel Admin <=>
    indexed_outcome_shape Q /\ indexed_ok_exit A R Q /\
    indexed_base A R InstPair Q /\
    phase_push C C' A R Run InstPair PushRel /\
    indexed_pop A R Q PushRel /\ indexed_call_exit A R Q PushRel /\
    indexed_lookup A R BlockPair InstPair /\
    indexed_admin_entry A R Admin /\ indexed_admin_refl Admin /\
    indexed_splice Q Admin /\ indexed_halted Q /\ indexed_halt Q /\
    indexed_increment A R BlockPair InstPair Q Admin /\
    phase_phi_prefix Run A R BlockPair Q /\
    phase_block_return C C' Run BlockPair Q
End

(* Run has a separate entry boundary: no PHI restart is demanded from
   intermediate block states, including exceptional terminal corridors. *)
Theorem phase_finite_induction:
  (!C i s r. finite_step C i s r ==>
    !C' A R Run BlockPair InstPair Q PushRel Admin (g:'g) j t.
    phase_contract C C' A R Run BlockPair InstPair Q PushRel Admin /\
    indexed_entry A R g s t /\ InstPair g i j ==>
    ?h r'. finite_step C' j t r' /\ Q g h r r') /\
  (!C bb s r. finite_block C bb s r ==>
    !C' A R Run BlockPair InstPair Q PushRel Admin (g:'g) bb' t.
    phase_contract C C' A R Run BlockPair InstPair Q PushRel Admin /\
    indexed_entry A R g s t /\ BlockPair bb bb' ==>
    ?h r'. finite_block C' bb' t r' /\ Q g h r r') /\
  (!C fn s r. finite_run C fn s r ==>
    !C' A R Run BlockPair InstPair Q PushRel Admin (g:'g) fn' t.
    phase_contract C C' A R Run BlockPair InstPair Q PushRel Admin /\
    Run g fn fn' s t ==>
    ?h r'. finite_run C' fn' t r' /\ Q g h r r')
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

Resume phase_finite_induction[base]:
  rpt strip_tac >> fs[phase_contract_def] >>
  qpat_x_assum `indexed_base _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_base_def] >> disch_then drule_all >> strip_tac >>
  qexistsl_tac [`h`, `r'`] >> simp[] >>
  irule finite_step_base >> simp[] >>
  qpat_x_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[]
QED

Resume phase_finite_induction[invoke_return]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_push _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_push_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_pop_elim >> strip_tac >>
  qexistsl_tac [`h'`, `OK out'`] >> simp[] >>
  irule finite_step_invoke_return >> metis_tac[]
QED
Resume phase_finite_induction[invoke_exit]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_push _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_push_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule indexed_call_exit_elim >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_invoke_exit >> simp[] >> metis_tac[]
QED
Resume phase_finite_induction[block_term]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_halted_elim >> strip_tac >>
  rename1 `Q g h (OK post) (OK target)` >>
  qexistsl_tac [`h`, `if target.vs_halted then Halt target else OK target`] >>
  conj_tac >- (irule finite_step_block_term >> metis_tac[]) >>
  Cases_on `post.vs_halted` >> fs[] >> metis_tac[indexed_halt_elim]
QED
Resume phase_finite_induction[block_next]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
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
Resume phase_finite_induction[block_exit]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >>
  irule finite_step_block_exit >> simp[] >> metis_tac[]
QED
Resume phase_finite_induction[run_next]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_phi_prefix _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_phi_prefix_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  `Run h' fn fn' s' t'` by
    (qpat_x_assum `phase_block_return _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[phase_block_return_def] >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `!C' A R Run BlockPair InstPair Q PushRel Admin g fn' t. _`
    drule_all >> strip_tac >>
  drule_all indexed_halted_elim >> strip_tac >>
  `Admin h' h' s' t' s' t'` by metis_tac[indexed_admin_refl_elim] >>
  drule_all indexed_splice_elim >> strip_tac >>
  qpat_x_assum `!d r r'. Q h d r r' ==> Q g d r r'` drule >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_run_next >> metis_tac[]

QED
Resume phase_finite_induction[run_halt]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_phi_prefix _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_phi_prefix_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_halted_elim >> strip_tac >>
  drule_all indexed_halt_elim >> strip_tac >>
  qpat_x_assum `!d r r'. Q h d r r' ==> Q g d r r'` drule >> strip_tac >>
  qexistsl_tac [`h'`, `Halt t'`] >> simp[] >>
  irule finite_step_run_halt >> metis_tac[]
QED
Resume phase_finite_induction[run_exit]:
  rpt strip_tac >>
  qpat_assum `phase_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_contract_def] >> strip_tac >>
  qpat_x_assum `phase_phi_prefix _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[phase_phi_prefix_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  qpat_x_assum `!d r r'. Q h d r r' ==> Q g d r r'` drule >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_run_exit >> simp[] >> metis_tac[]
QED
Finalise phase_finite_induction

Theorem phase_finite_simulation:
  phase_contract C C' A R Run BlockPair InstPair Q PushRel Admin ==>
  phase_simulates C C' A R Run BlockPair InstPair Q
Proof
  simp[phase_simulates_def] >> metis_tac[phase_finite_induction]
QED

Theorem phase_run_simulation:
  phase_contract C C' A R Run BlockPair InstPair Q PushRel Admin /\
  Run (g:'g) fn fn' s t /\ (!e. run_blocks n C fn s <> Error e) ==>
  ?m (h:'g) r'. run_blocks m C' fn' t = r' /\ Q g h (run_blocks n C fn s) r'
Proof
  rpt strip_tac >>
  `finite_run C fn s (run_blocks n C fn s)` by metis_tac[finite_run_iff] >>
  drule (cj 3 phase_finite_induction) >>
  disch_then drule >> disch_then drule >> strip_tac >>
  fs[finite_run_iff] >> metis_tac[]
QED

val _ = export_theory();
