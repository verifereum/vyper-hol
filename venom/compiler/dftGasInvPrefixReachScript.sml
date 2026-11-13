Theory dftGasInvPrefixReach
Ancestors
  dftGasInvPrefixRun dftGasInvCallBoundary dftGasOracleDefs
  venomInstProofs1 venomExecSemantics contextCodegenRel

Theorem ev_step_nonterm_current_bb:
  ~is_terminator inst.inst_opcode /\
  ev_step orc p d fuel C inst s = OK u ==>
  u.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all ev_step_invoke_OK >> strip_tac >>
      mp_tac (Q.ISPEC `\s:venom_state. s.vs_current_bb` bind_outputs_preserves) >>
      simp[venomStateTheory.update_var_def, adopt_return_fmp_def,
           merge_callee_state_def] >>
      disch_then drule >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (gvs[ev_step_def, ev_gas_def, AllCaseEqs(),
          venomStateTheory.update_var_def]) >>
  gvs[ev_step_def] >> drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem inv_ev_prefix_reachable:
  !n s t first_inst last_inst.
    inv_ev_prefix orc p d C bb n s t /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    ev_reachable orc s0 C p d fn first_inst s /\
    get_instruction bb s.vs_inst_idx = SOME first_inst /\
    get_instruction bb t.vs_inst_idx = SOME last_inst ==>
    ev_reachable orc s0 C p d fn last_inst t
Proof
  Induct >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> pure_rewrite_tac[inv_ev_prefix_suc] >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule_all ev_step_nonterm_current_bb >> simp[]) >>
  Cases_on `n`
  >- (gvs[] >> irule ev_reachable_next >>
      conj_tac
      >- (simp[active_inst_def] >> qexists_tac `bb` >>
          gvs[venomInstTheory.get_instruction_def]) >>
      qexistsl_tac [`fuel`, `first_inst`] >>
      simp[active_inst_def] >> qexists_tac `bb` >>
      gvs[venomInstTheory.get_instruction_def]) >>
  qpat_assum `inv_ev_prefix _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[inv_ev_prefix_suc] >> strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `inst'` >> simp[] >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >> simp[] >>
  irule ev_reachable_next >>
  conj_tac
  >- (simp[active_inst_def] >> qexists_tac `bb` >>
      gvs[venomInstTheory.get_instruction_def]) >>
  qexistsl_tac [`fuel`, `first_inst`] >>
  gvs[] >> simp[active_inst_def] >> qexists_tac `bb` >>
  gvs[venomInstTheory.get_instruction_def]
QED
