Theory makeSsaCurrentCleanupBoundary
Ancestors
  makeSsaCurrentDefs makeSsaCurrentEdgeTrace makeSsaCurrentTraceCertificate
  venomInst irSupply list pair

Theorem current_phi_slots_remove_self:
  !slots. remove_current_phi_self out (current_phi_slots slots) =
    current_phi_slots (FILTER (\slot. SND slot <> out) slots)
Proof
  Induct >> simp[current_phi_slots_def, remove_current_phi_self_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_phi_slots_def, remove_current_phi_self_def] >>
  Cases_on `h1 = out` >> fs[current_phi_slots_def]
QED

Theorem current_phi_slots_values:
  !slots. current_phi_values (current_phi_slots slots) = SOME (MAP SND slots)
Proof
  Induct >> simp[current_phi_slots_def, current_phi_values_def] >>
  gen_tac >> PairCases_on `h` >>
  fs[current_phi_slots_def, current_phi_values_def]
QED

Theorem current_phi_slots_retained:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  MEM (p,a) slots /\ MEM (q,b) slots /\
  a <> b /\ a <> out /\ b <> out ==>
  simplify_current_phi inst = inst
Proof
  strip_tac >>
  `MEM a (MAP SND (FILTER (\slot. SND slot <> out) slots)) /\
   MEM b (MAP SND (FILTER (\slot. SND slot <> out) slots))` by
    (simp[MEM_MAP, MEM_FILTER] >> metis_tac[SND]) >>
  qmatch_asmsub_abbrev_tac `MEM a vals` >>
  `simplify_current_phi_raw inst = inst` by
    (simp[simplify_current_phi_raw_def, current_phi_output_def,
       current_phi_slots_remove_self, current_phi_slots_values] >>
     Cases_on `vals` >> fs[] >>
     IF_CASES_TAC >> fs[EVERY_MEM] >> metis_tac[]) >>
  simp[simplify_current_phi_def, keep_current_phi_vars_def, EVERY_MEM]
QED

Theorem current_phi_slots_empty:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  FILTER (\slot. SND slot <> out) slots = [] ==>
  simplify_current_phi inst =
    inst with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>
Proof
  strip_tac >>
  simp[simplify_current_phi_def, simplify_current_phi_raw_def,
    current_phi_output_def, current_phi_slots_remove_self, current_phi_slots_values,
    keep_current_phi_vars_def, inst_ir_vars_def, inst_uses_def,
    venomInstTheory.operand_vars_def]
QED

Theorem current_phi_slots_constant:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  MAP SND (FILTER (\slot. SND slot <> out) slots) = v::vs /\
  EVERY (\w. w = v) vs ==>
  simplify_current_phi inst =
    inst with <|inst_opcode := ASSIGN; inst_operands := [Var v]|>
Proof
  strip_tac >>
  `MEM v (MAP SND slots)` by
    (`MEM v (MAP SND (FILTER (\slot. SND slot <> out) slots))` by simp[] >>
     fs[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  simp[simplify_current_phi_def, simplify_current_phi_raw_def,
    current_phi_output_def, current_phi_slots_remove_self, current_phi_slots_values,
    keep_current_phi_vars_def, inst_ir_vars_def, inst_uses_def,
    venomInstTheory.operand_vars_def, operand_var_def, current_phi_slots_vars]
QED

Theorem current_phi_prefix_partition:
  !prefix suffix.
  EVERY (\inst. inst.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) ==>
  simplify_current_phi_prefix_parts (prefix ++ suffix) =
    (FILTER (\inst. inst.inst_opcode = PHI) (MAP simplify_current_phi prefix),
     FILTER (\inst. inst.inst_opcode <> PHI) (MAP simplify_current_phi prefix) ++ suffix)
Proof
  Induct
  >- (Cases >> simp[simplify_current_phi_prefix_parts_def]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `suffix` mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  gvs[EVERY_DEF] >>
  simp[simplify_current_phi_prefix_parts_def] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >> simp[]
QED

Theorem current_phi_prefix_parts_length:
  !insts phis ordinary.
  simplify_current_phi_prefix_parts insts = (phis,ordinary) ==>
  LENGTH phis + LENGTH ordinary = LENGTH insts
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `simplify_current_phi_prefix_parts insts` >> simp[] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  simp[] >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem current_reassign_length[simp]:
  !ids insts. LENGTH (reassign_current_inst_ids ids insts) = LENGTH insts
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_reassign_content:
  !ids insts k. k < LENGTH insts ==>
  (EL k (reassign_current_inst_ids ids insts)).inst_opcode = (EL k insts).inst_opcode /\
  (EL k (reassign_current_inst_ids ids insts)).inst_operands = (EL k insts).inst_operands /\
  (EL k (reassign_current_inst_ids ids insts)).inst_outputs = (EL k insts).inst_outputs
Proof
  Induct >> simp[reassign_current_inst_ids_def] >> Cases_on `insts` >>
  simp[reassign_current_inst_ids_def] >> Cases_on `k` >> simp[]
QED

Theorem current_phi_prefix_length[simp]:
  LENGTH (simplify_current_phi_prefix insts) = LENGTH insts
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> simp[] >>
  drule current_phi_prefix_parts_length >> simp[]
QED
