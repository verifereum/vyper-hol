(* Structural control boundaries for expansion prefixes. *)
Theory lowerDloadEnvelopeControl
Ancestors
  lowerDloadSafetyLocations lowerDloadSafetyKernel lowerDloadPublicTrace lowerDloadDefs lowerDloadSafetyRelation
  venomExecProofs venomInstProps venomExecSemantics venomInst o1ContractLowerDload list

Theorem ld_prefix_control:
  !h t. ld_prefix C fn X p h t0 t /\
    EVERY (\i. ~is_terminator i.inst_opcode) X ==>
    t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb
Proof
  Induct_on `h`
  >- simp[lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
  rpt strip_tac >> dxrule ld_prefix_predecessor >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac)) >>
  first_x_assum drule_all >> strip_tac >>
  `~is_terminator (EL h X).inst_opcode` by
    (drule ld_prefix_bound >> strip_tac >> gvs[EVERY_EL]) >>
  drule_all step_preserves_control_flow >> strip_tac >> gvs[]
QED

Theorem ld_envelope_nonterminal:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\
  ld_envelope supply fn s s.vs_inst_idx X p /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) X
Proof
  strip_tac >>
  qpat_x_assum `ld_envelope _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ld_envelope_def] >> strip_tac >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[contextCodegenRelTheory.active_inst_def] >> strip_tac >>
  `bb = bb'` by
    (irule ld_block_label_unique >> conj_tac >- simp[] >>
     qexists_tac `fn.fn_blocks` >> simp[] >> metis_tac[MEM_EL]) >> gvs[] >>
  qmatch_goalsub_abbrev_tac `lower_dload_inst_supply su ii` >>
  Cases_on `ii.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def])) >>
  Cases_on `ii.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def])) >>
  gvs[lower_dload_inst_supply_def]
QED
