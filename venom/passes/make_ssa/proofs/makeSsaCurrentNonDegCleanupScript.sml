Theory makeSsaCurrentNonDegCleanup
Ancestors
  makeSsaCurrentCleanupBoundary makeSsaCurrentDefs venomInst venomWf list pair

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
