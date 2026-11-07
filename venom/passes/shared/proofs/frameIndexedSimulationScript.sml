Theory frameIndexedSimulation
Ancestors frameIndexedComposition frameIndexedCertificates frameFiniteExecution

Definition indexed_contract_def:
  indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin <=>
    indexed_outcome_shape Q /\ indexed_ok_exit A R Q /\
    indexed_base A R InstPair Q /\
    indexed_push C C' A R (\g fn fn'. FnPair fn fn') InstPair PushRel /\
    indexed_pop A R Q PushRel /\ indexed_call_exit A R Q PushRel /\
    indexed_composition A R FnPair BlockPair InstPair Q Admin
End

Theorem indexed_finite_simulation:
  (!C i s r. finite_step C i s r ==>
    !C' A R FnPair BlockPair InstPair Q PushRel Admin (g:'g) j t.
    indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin /\
    indexed_entry A R (g:'g) s t /\ InstPair g i j ==>
    ?h r'. finite_step C' j t r' /\ Q g h r r') /\
  (!C bb s r. finite_block C bb s r ==>
    !C' A R FnPair BlockPair InstPair Q PushRel Admin (g:'g) bb' t.
    indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin /\
    indexed_entry A R (g:'g) s t /\ BlockPair bb bb' ==>
    ?h r'. finite_block C' bb' t r' /\ Q g h r r') /\
  (!C fn s r. finite_run C fn s r ==>
    !C' A R FnPair BlockPair InstPair Q PushRel Admin (g:'g) fn' t.
    indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin /\
    indexed_entry A R (g:'g) s t /\ FnPair fn fn' ==>
    ?h r'. finite_run C' fn' t r' /\ Q g h r r')
Proof
  ho_match_mp_tac finite_step_ind >> rpt conj_tac
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

Resume indexed_finite_simulation[base]:
  rpt strip_tac >>
  fs[indexed_contract_def] >>
  qpat_x_assum `indexed_base _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_base_def] >> disch_then drule_all >> strip_tac >>
  qexistsl_tac [`h`, `r'`] >> simp[] >>
  irule finite_step_base >> simp[] >>
  qpat_x_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[]
QED

Resume indexed_finite_simulation[invoke_return]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def] >> strip_tac >>
  drule_all indexed_push_elim >> strip_tac >> fs[] >>
  first_x_assum drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_pop_elim >> strip_tac >>
  qexistsl_tac [`h'`, `OK out'`] >> simp[] >>
  irule finite_step_invoke_return >> metis_tac[]
QED

Resume indexed_finite_simulation[invoke_exit]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def] >> strip_tac >>
  drule_all indexed_push_elim >> strip_tac >> fs[] >>
  first_x_assum drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  qpat_x_assum `indexed_entry A R c _ _` kall_tac >>
  drule indexed_call_exit_elim >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_invoke_exit >> simp[] >> metis_tac[]
QED

Resume indexed_finite_simulation[block_term]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def, indexed_composition_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all indexed_halted_elim >> strip_tac >>
  rename1 `Q g h (OK post) (OK target)` >>
  qexistsl_tac [`h`, `if target.vs_halted then Halt target else OK target`] >>
  conj_tac >- (irule finite_step_block_term >> metis_tac[]) >>
  Cases_on `post.vs_halted` >> fs[] >> metis_tac[indexed_halt_elim]
QED

Resume indexed_finite_simulation[block_next]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def, indexed_composition_def] >> strip_tac >>
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

Resume indexed_finite_simulation[block_exit]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def, indexed_composition_def] >> strip_tac >>
  drule_all indexed_lookup_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >>
  irule finite_step_block_exit >> simp[] >> metis_tac[]
QED

Resume indexed_finite_simulation[run_exit]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def, indexed_composition_def] >> strip_tac >>
  drule_all indexed_phi_prefix_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  qpat_x_assum `!d r r'. Q h d r r' ==> Q g d r r'` drule >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_run_exit >> simp[] >> metis_tac[]
QED

Resume indexed_finite_simulation[run_halt]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def, indexed_composition_def] >> strip_tac >>
  drule_all indexed_phi_prefix_elim >> strip_tac >>
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

Resume indexed_finite_simulation[run_next]:
  rpt strip_tac >>
  qpat_assum `indexed_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_contract_def, indexed_composition_def] >> strip_tac >>
  drule_all indexed_phi_prefix_elim >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `indexed_outcome_shape _` mp_tac >>
  pure_rewrite_tac[indexed_outcome_shape_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  qpat_assum `indexed_ok_exit _ _ _` mp_tac >>
  pure_rewrite_tac[indexed_ok_exit_def] >> disch_then drule >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all indexed_halted_elim >> strip_tac >>
  `Admin h' h' s' t' s' t'` by metis_tac[indexed_admin_refl_elim] >>
  qpat_x_assum `Q h h' (OK s') (OK t')` kall_tac >>
  drule_all indexed_splice_elim >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule finite_step_run_next >> metis_tac[]
QED

Finalise indexed_finite_simulation

Theorem indexed_step_simulation:
  indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin /\
  indexed_entry A R (g:'g) s t /\ InstPair g i j /\
  (!e. step_inst n C i s <> Error e) ==>
  ?m (h:'g) r'. step_inst m C' j t = r' /\ Q g h (step_inst n C i s) r'
Proof
  rpt strip_tac >>
  `finite_step C i s (step_inst n C i s)` by metis_tac[finite_step_iff] >>
  drule (cj 1 indexed_finite_simulation) >> disch_then drule_all >> strip_tac >>
  fs[finite_step_iff] >> metis_tac[]
QED

Theorem indexed_block_simulation:
  indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin /\
  indexed_entry A R (g:'g) s t /\ BlockPair bb bb' /\
  (!e. exec_block n C bb s <> Error e) ==>
  ?m (h:'g) r'. exec_block m C' bb' t = r' /\ Q g h (exec_block n C bb s) r'
Proof
  rpt strip_tac >>
  `finite_block C bb s (exec_block n C bb s)` by metis_tac[finite_block_iff] >>
  drule (cj 2 indexed_finite_simulation) >> disch_then drule_all >> strip_tac >>
  fs[finite_block_iff] >> metis_tac[]
QED

Theorem indexed_run_simulation:
  indexed_contract C C' A R FnPair BlockPair InstPair Q PushRel Admin /\
  indexed_entry A R (g:'g) s t /\ FnPair fn fn' /\
  (!e. run_blocks n C fn s <> Error e) ==>
  ?m (h:'g) r'. run_blocks m C' fn' t = r' /\ Q g h (run_blocks n C fn s) r'
Proof
  rpt strip_tac >>
  `finite_run C fn s (run_blocks n C fn s)` by metis_tac[finite_run_iff] >>
  drule (cj 3 indexed_finite_simulation) >> disch_then drule_all >> strip_tac >>
  fs[finite_run_iff] >> metis_tac[]
QED

Theorem indexed_identity_run_simulation:
  (!e. run_blocks n C fn s <> Error e) ==>
  ?m. run_blocks m C fn s = run_blocks n C fn s
Proof
  strip_tac >>
  `indexed_contract C C (\g s. T) (\g s t. s = t)
     (\fn fn'. fn = fn') (\bb bb'. bb = bb') (\g i j. i = j)
     identity_outcome identity_push identity_admin` by
    (pure_rewrite_tac[indexed_contract_def] >> BETA_TAC >>
     MATCH_ACCEPT_TAC indexed_identity_complete) >>
  drule indexed_run_simulation >>
  simp[indexed_entry_def, identity_outcome_def] >>
  metis_tac[]
QED

val _ = export_theory();
