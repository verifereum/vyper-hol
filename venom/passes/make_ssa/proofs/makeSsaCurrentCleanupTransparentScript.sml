Theory makeSsaCurrentCleanupTransparent
Ancestors
  makeSsaCurrentCleanupBoundary makeSsaCurrentNonDegCleanup makeSsaCurrentRetainedEffect
  makeSsaCurrentLockstepShape makeSsaCurrentNonDegTransport
  makeSsaCurrentDefs makeSsaCurrentWfSsa makeSsaHelper venomExecProps venomWf
  makeSsaCurrentEdgeTrace o1FrameLockstep venomExecSemantics venomInst list

Theorem current_nondeg_phi_fixed:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  phi_well_formed inst.inst_operands /\
  MEM (p,a) (phi_pairs inst.inst_operands) /\
  MEM (q,b) (phi_pairs inst.inst_operands) /\
  a <> out /\ b <> out /\ a <> b ==>
  simplify_current_phi inst = inst
Proof
  strip_tac >> irule current_phi_slots_retained >>
  simp[] >> qexistsl_tac [`a`, `b`, `p`, `q`, `phi_pairs inst.inst_operands`] >>
  simp[current_nondeg_slots_decode]
QED

Theorem current_fixed_phi_parts:
  !insts. EVERY (\inst. inst.inst_opcode = PHI ==> simplify_current_phi inst = inst) insts ==>
  FST (simplify_current_phi_prefix_parts insts) ++
  SND (simplify_current_phi_prefix_parts insts) = insts
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `simplify_current_phi_prefix_parts insts` >> gvs[]
QED

Theorem current_fixed_phi_cleanup_effect:
  EVERY (\inst. inst.inst_opcode = PHI ==> simplify_current_phi inst = inst) bb.bb_instructions ==>
  phi_eff prev z (simplify_current_phi_block bb).bb_instructions =
  phi_eff prev z bb.bb_instructions
Proof
  strip_tac >> drule current_fixed_phi_parts >> strip_tac >>
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_def] >>
  Cases_on `simplify_current_phi_prefix_parts (h::t)` >>
  gvs[phi_eff_def, current_retained_reassign_read]
QED

Theorem current_fixed_phi_cleanup_prefix:
  EVERY (\inst. inst.inst_opcode = PHI ==> simplify_current_phi inst = inst) bb.bb_instructions ==>
  phi_prefix_length (simplify_current_phi_block bb).bb_instructions =
  phi_prefix_length bb.bb_instructions
Proof
  strip_tac >> drule current_fixed_phi_parts >> strip_tac >>
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_def] >>
  Cases_on `simplify_current_phi_prefix_parts (h::t)` >>
  gvs[reassign_current_inst_ids_phi_prefix]
QED

Theorem current_phi_free_context_fixed:
  current_wf_phi_context s fn renamed s' A H events /\
  ~blocks_have_leading_phi fn.fn_blocks /\ entry_block fn = SOME eb /\
  lookup_block h renamed = SOME new ==>
  EVERY (\inst. inst.inst_opcode = PHI ==> simplify_current_phi inst = inst)
    new.bb_instructions
Proof
  strip_tac >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `MEM new renamed /\ new.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule_all current_wf_phi_context_lookup >> strip_tac >> gvs[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `?q. q < LENGTH new.bb_instructions /\ inst = EL q new.bb_instructions` by
    metis_tac[MEM_EL] >>
  qpat_x_assum `inst = EL q _` SUBST_ALL_TAC >>
  `?v. current_wf_inserted_phi_at A renamed new.bb_label q v` by
    (drule_all current_wf_phi_occurrence_provenance >>
     metis_tac[current_nondeg_no_original_phi]) >>
  drule_all current_wf_inserted_phi_output >> strip_tac >>
  drule_all current_wf_inserted_phi_slots >> strip_tac >>
  drule_all current_nondeg_inserted_phi >> strip_tac >>
  `!slots. phi_well_formed (current_phi_slots slots)` by
    (Induct >> simp[current_phi_slots_def, phi_well_formed_def] >>
     gen_tac >> PairCases_on `h` >> fs[current_phi_slots_def, phi_well_formed_def]) >>
  irule current_nondeg_phi_fixed >> simp[] >> metis_tac[]
QED
