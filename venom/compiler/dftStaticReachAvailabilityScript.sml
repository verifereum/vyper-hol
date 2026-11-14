(* Availability depends on successful prefixes, so the existing non-static
   theorem can be applied to each prefix's shadow. *)
Theory dftStaticReachAvailability
Ancestors
  staticShadowEventReachable staticShadowO1State staticShadowDefs
  dftStaticShadowObservation dftGasInvReachAvailability dftGasOracleDefs
  dftRunRel o1PassContract unitTransformDefs lowerDloadDefs venomWfProps venomState

Theorem inv_ev_reachable_source_available_static:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ ctx_labels_bound C initial.vs_labels /\
  o1_initial_state_ok initial /\ initial.vs_fmp = initial.vs_initial_fmp /\
  code_layout_valid initial /\ ev_reachable orc initial C p d fn inst t ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  strip_tac >> Cases_on `initial.vs_call_ctx.cc_static`
  >- (drule_all static_shadow_ev_reachable >> strip_tac >>
      rename1 `static_shadow_rel t th` >>
      `o1_run_state_ok (static_shadow initial)` by
        (irule static_shadow_o1_run_state_ok >> simp[]) >>
      `ctx_labels_bound C (static_shadow initial).vs_labels` by
        simp[static_shadow_def] >>
      `fn_reachable fn th.vs_current_bb /\ strict_dom_vars_defined fn th` by
        (irule inv_ev_reachable_source_available >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      gvs[static_shadow_rel_def, static_shadow_def,
          venom_state_component_equality, strict_dom_vars_defined_def] >> first_assum ACCEPT_TAC) >>
  irule inv_ev_reachable_source_available >>
  goal_assum (drule_at Any) >> simp[o1_run_state_ok_def] >> metis_tac[]
QED

Theorem inv_ev_reachable_source_initialized_static:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ ctx_labels_bound C initial.vs_labels /\
  o1_initial_state_ok initial /\ initial.vs_fmp = initial.vs_initial_fmp /\
  code_layout_valid initial /\ ev_reachable orc initial C p d fn inst t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  t.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
  dft_remaining_inv fn bb (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) t
Proof
  strip_tac >> Cases_on `initial.vs_call_ctx.cc_static`
  >- (drule_all static_shadow_ev_reachable >> strip_tac >>
      rename1 `static_shadow_rel t th` >>
      `o1_run_state_ok (static_shadow initial)` by
        (irule static_shadow_o1_run_state_ok >> simp[]) >>
      `ctx_labels_bound C (static_shadow initial).vs_labels` by
        simp[static_shadow_def] >>
      `th.vs_current_bb = t.vs_current_bb /\ th.vs_inst_idx = t.vs_inst_idx` by
        gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
      `dft_remaining_inv fn bb
         (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) th` by
        (irule inv_ev_reachable_source_initialized >> gvs[] >> metis_tac[]) >>
      metis_tac[static_shadow_remaining_inv]) >>
  irule inv_ev_reachable_source_initialized >>
  goal_assum (drule_at Any) >> simp[o1_run_state_ok_def] >> metis_tac[]
QED
