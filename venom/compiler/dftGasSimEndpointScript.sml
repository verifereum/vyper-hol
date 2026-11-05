Theory dftGasSimEndpoint
Ancestors
  dftGasSimInvariant dftGasSimBoundary dftGasOracleDefs
  venomExecProofs venomExecSemantics venomState venomInst
  list pred_set finite_map

Theorem ev_step_fdom_mono:
  ev_step orc p d fuel C inst s = OK t /\ inst_wf inst ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (`inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      `step_inst fuel C inst s = OK t` by
        gvs[Once ev_step_def, step_inst_non_invoke] >>
      gvs[SUBSET_DEF] >> rpt strip_tac >>
      drule_all step_terminator_preserves_vars >>
      disch_then (qspec_then `x` mp_tac) >>
      gvs[lookup_var_def, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  Cases_on `inst.inst_opcode = PHI`
  >- gvs[Once ev_step_def, step_inst_base_phi_error] >>
  drule_all ev_step_fdom >> simp[SUBSET_DEF]
QED

Theorem ev_suffix_fdom_mono:
  !xs s t. EVERY inst_wf xs /\ ev_suffix orc p d fuel C xs s = OK t ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  Induct >> simp[ev_suffix_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `ev_step orc p d fuel C h s` >> gvs[] >>
  drule_all ev_step_fdom_mono >> strip_tac >>
  Cases_on `is_terminator h.inst_opcode`
  >- (Cases_on `v.vs_halted` >> gvs[]) >>
  gvs[] >> first_x_assum drule >> simp[] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem ev_block_fdom_mono:
  ev_block orc p d fuel C bb s = OK t /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  strip_tac >>
  mp_tac (ev_suffix_block |> Q.INST [`ctx` |-> `C`]) >>
  disch_then (qspecl_then [`DROP s.vs_inst_idx bb.bb_instructions`, `s`, `bb`] mp_tac) >>
  simp[] >> strip_tac >>
  irule ev_suffix_fdom_mono >>
  goal_assum (drule_at Any) >>
  `EVERY inst_wf (TAKE s.vs_inst_idx bb.bb_instructions ++
     DROP s.vs_inst_idx bb.bb_instructions)` by
       (pure_rewrite_tac[TAKE_DROP] >> simp[]) >>
  gvs[EVERY_APPEND]
QED
