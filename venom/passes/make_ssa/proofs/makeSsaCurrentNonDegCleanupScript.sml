Theory makeSsaCurrentNonDegCleanup
Ancestors
  makeSsaCurrentCleanupBoundary makeSsaCurrentDefs unitShapeDefs venomInst venomWf list pair

Definition current_nondeg_block_shape_def:
  current_nondeg_block_shape bb <=>
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = PHI ==>
      (EL i bb.bb_instructions).inst_opcode = PHI) /\
    EVERY (\inst. inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands)
      bb.bb_instructions
End

Theorem current_nondeg_input_shape:
  wf_function fn /\ fn_inst_wf fn ==>
  EVERY current_nondeg_block_shape fn.fn_blocks
Proof
  simp[EVERY_MEM, current_nondeg_block_shape_def] >>
  rpt strip_tac
  >- (fs[wf_function_def, bb_well_formed_def] >> metis_tac[]) >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  gvs[inst_wf_def]
QED

Theorem current_nondeg_retained_slots:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  (simplify_current_phi inst).inst_opcode = PHI ==>
  ?p a q b. MEM (p,a) slots /\ MEM (q,b) slots /\
    a <> out /\ b <> out /\ a <> b
Proof
  strip_tac >>
  Cases_on `MAP SND (FILTER (\slot. SND slot <> out) slots)`
  >- (`FILTER (\slot. SND slot <> out) slots = []` by metis_tac[MAP_EQ_NIL] >>
      drule_all current_phi_slots_empty >> strip_tac >> gvs[]) >>
  rename1 `MAP SND (FILTER (\slot. SND slot <> out) slots) = a::vs` >>
  Cases_on `EVERY (\w. w = a) vs`
  >- (drule_all current_phi_slots_constant >> strip_tac >> gvs[]) >>
  `?b. MEM b vs /\ b <> a` by (fs[EXISTS_MEM] >> metis_tac[]) >>
  `MEM a (MAP SND (FILTER (\slot. SND slot <> out) slots)) /\
   MEM b (MAP SND (FILTER (\slot. SND slot <> out) slots))` by simp[] >>
  fs[MEM_MAP, MEM_FILTER] >>
  PairCases_on `y` >> PairCases_on `y'` >> gvs[] >> metis_tac[]
QED

Theorem current_nondeg_slots_decode:
  !ops. phi_well_formed ops ==>
    current_phi_slots (phi_pairs ops) = ops
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_well_formed_def, phi_pairs_def,
       makeSsaCurrentEdgeTraceTheory.current_phi_slots_def]
QED

Theorem current_nondeg_retained_content:
  (simplify_current_phi inst).inst_opcode = PHI ==>
  simplify_current_phi inst = inst
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[simplify_current_phi_raw_def] >>
  Cases_on `inst.inst_opcode <> PHI` >> simp[] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >> simp[] >>
  Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem current_nondeg_retained_pairs:
  phi_well_formed inst.inst_operands /\
  (simplify_current_phi inst).inst_opcode = PHI /\
  (simplify_current_phi inst).inst_outputs = [out] ==>
  ?p a q b.
    MEM (p,a) (phi_pairs (simplify_current_phi inst).inst_operands) /\
    MEM (q,b) (phi_pairs (simplify_current_phi inst).inst_operands) /\
    a <> out /\ b <> out /\ a <> b
Proof
  strip_tac >> drule current_nondeg_retained_content >> strip_tac >> gvs[] >>
  irule current_nondeg_retained_slots >>
  simp[current_nondeg_slots_decode] >> metis_tac[]
QED

Theorem current_nondeg_reassign:
  !ids insts.
  EVERY (\inst. !out. inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    ?p a q b. MEM (p,a) (phi_pairs inst.inst_operands) /\
      MEM (q,b) (phi_pairs inst.inst_operands) /\
      a <> out /\ b <> out /\ a <> b) insts ==>
  EVERY (\inst. !out. inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    ?p a q b. MEM (p,a) (phi_pairs inst.inst_operands) /\
      MEM (q,b) (phi_pairs inst.inst_operands) /\
      a <> out /\ b <> out /\ a <> b)
    (reassign_current_inst_ids ids insts)
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_nondeg_clean_prefix:
  EVERY (\inst. inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands) prefix /\
  EVERY (\inst. inst.inst_opcode <> PHI) suffix ==>
  EVERY (\inst. !out. inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    ?p a q b. MEM (p,a) (phi_pairs inst.inst_operands) /\
      MEM (q,b) (phi_pairs inst.inst_operands) /\
      a <> out /\ b <> out /\ a <> b)
    (simplify_current_phi_prefix (prefix ++ suffix))
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI) prefix` by fs[EVERY_MEM] >>
  `suffix = [] \/ (HD suffix).inst_opcode <> PHI` by
    (Cases_on `suffix` >> fs[]) >>
  `simplify_current_phi_prefix_parts (prefix ++ suffix) =
    (FILTER (\inst. inst.inst_opcode = PHI) (MAP simplify_current_phi prefix),
     FILTER (\inst. inst.inst_opcode <> PHI) (MAP simplify_current_phi prefix) ++ suffix)` by
    (irule current_phi_prefix_partition >> simp[]) >>
  simp[simplify_current_phi_prefix_def] >> irule current_nondeg_reassign >>
  simp[EVERY_APPEND, EVERY_FILTER, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[EVERY_MEM] >>
  irule current_nondeg_retained_pairs >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_nondeg_prefix_decompose:
  !insts.
  (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
    (EL i insts).inst_opcode = PHI) ==>
  ?prefix suffix. insts = prefix ++ suffix /\
    EVERY (\inst. inst.inst_opcode = PHI) prefix /\
    EVERY (\inst. inst.inst_opcode <> PHI) suffix
Proof
  Induct >- (rpt strip_tac >> qexistsl [`[]`, `[]`] >> simp[]) >>
  gen_tac >> disch_tac >>
  `!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
    (EL i insts).inst_opcode = PHI` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (qexistsl [`h::prefix`, `suffix`] >> simp[]) >>
  qexistsl [`[]`, `h::insts`] >> simp[EVERY_MEM, MEM_EL] >>
  rpt strip_tac >>
  qpat_x_assum `!i j. _ /\ j < LENGTH (h::insts) /\ _ ==> _`
    (qspecl_then [`0`, `SUC n`] mp_tac) >> gvs[]
QED

Theorem current_nondeg_clean_block:
  current_nondeg_block_shape bb ==>
  EVERY (\inst. !out. inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    ?p a q b. MEM (p,a) (phi_pairs inst.inst_operands) /\
      MEM (q,b) (phi_pairs inst.inst_operands) /\
      a <> out /\ b <> out /\ a <> b)
    (simplify_current_phi_block bb).bb_instructions
Proof
  rewrite_tac[current_nondeg_block_shape_def] >> strip_tac >>
  `?prefix suffix. bb.bb_instructions = prefix ++ suffix /\
    EVERY (\inst. inst.inst_opcode = PHI) prefix /\
    EVERY (\inst. inst.inst_opcode <> PHI) suffix` by
    (irule current_nondeg_prefix_decompose >> fs[bb_well_formed_def]) >>
  `EVERY (\inst. inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands) prefix` by
    fs[EVERY_APPEND, EVERY_MEM] >>
  Cases_on `prefix`
  >- (simp[simplify_current_phi_block_def] >> Cases_on `suffix` >>
      gvs[EVERY_MEM] >> metis_tac[MEM]) >>
  drule_all current_nondeg_clean_prefix >>
  gvs[EVERY_DEF, simplify_current_phi_block_def]
QED

Theorem current_nondeg_cleanup_map:
  !bbs. simplify_current_phis bbs = MAP simplify_current_phi_block bbs
Proof
  gen_tac >> simp[simplify_current_phis_def] >> IF_CASES_TAC >> simp[] >>
  pop_assum mp_tac >> qid_spec_tac `bbs` >> Induct >>
  simp[blocks_have_leading_phi_def, simplify_current_phi_block_def] >>
  Cases_on `h.bb_instructions` >> simp[]
QED

Theorem current_nondeg_clean_blocks:
  EVERY current_nondeg_block_shape bbs ==>
  EVERY (\bb. EVERY (\inst. !out.
    inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    ?p a q b. MEM (p,a) (phi_pairs inst.inst_operands) /\
      MEM (q,b) (phi_pairs inst.inst_operands) /\
      a <> out /\ b <> out /\ a <> b) bb.bb_instructions)
    (simplify_current_phis_if T bbs)
Proof
  rewrite_tac[simplify_current_phis_if_def, current_nondeg_cleanup_map, EVERY_MAP] >>
  strip_tac >> irule EVERY_MONOTONIC >>
  qexists_tac `current_nondeg_block_shape` >>
  simp[] >> metis_tac[current_nondeg_clean_block]
QED

Theorem current_nondeg_clean_function:
  EVERY current_nondeg_block_shape fn.fn_blocks ==>
  fn_phis_non_degenerate
    (fn with fn_blocks := simplify_current_phis_if T fn.fn_blocks)
Proof
  strip_tac >> drule current_nondeg_clean_blocks >>
  simp[fn_phis_non_degenerate_def, fn_insts_def, MEM_fn_insts_blocks_iff,
       EVERY_MEM] >> metis_tac[]
QED
