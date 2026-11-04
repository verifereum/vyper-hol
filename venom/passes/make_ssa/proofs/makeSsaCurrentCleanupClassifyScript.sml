Theory makeSsaCurrentCleanupClassify
Ancestors makeSsaCurrentCleanupBoundary makeSsaCurrentDefs list

(* Reuse the existing slots encoder and cleanup branches. *)
Theorem current_phi_nonself_values:
  !ps. MAP SND (FILTER (\slot. SND slot <> out) ps) =
    FILTER (\v. v <> out) (MAP SND ps)
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  Cases_on `h1 = out` >> simp[]
QED

Theorem current_phi_slots_classify:
  i.inst_opcode = PHI /\ i.inst_outputs = [out] /\
  i.inst_operands = current_phi_slots ps /\
  ns = FILTER (\v. v <> out) (MAP SND ps) ==>
  simplify_current_phi i =
    case ns of
      [] => i with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>
    | v::vs => if EVERY (\w. w = v) vs then
        i with <|inst_opcode := ASSIGN; inst_operands := [Var v]|>
      else i
Proof
  strip_tac >> Cases_on `ns`
  >- (`FILTER (\slot. SND slot <> out) ps = []` by
        metis_tac[current_phi_nonself_values,listTheory.MAP_EQ_NIL] >>
      drule_all current_phi_slots_empty >> simp[NoAsms]) >>
  rename1 `v::vs = FILTER _ _` >>
  qpat_x_assum `v::vs = FILTER _ _` (assume_tac o SYM) >>
  Cases_on `EVERY (\w. w = v) vs`
  >- (`MAP SND (FILTER (\slot. SND slot <> out) ps) = v::vs` by
        metis_tac[current_phi_nonself_values] >>
      drule_all current_phi_slots_constant >> simp[NoAsms] >>
      simp[]) >>
  simp[] >>
  `simplify_current_phi_raw i = i` by
    (simp[simplify_current_phi_raw_def,current_phi_output_def,
       current_phi_slots_remove_self,current_phi_slots_values,
       current_phi_nonself_values] >> gvs[]) >>
  simp[simplify_current_phi_def,keep_current_phi_vars_def,EVERY_MEM]
QED

Theorem current_phi_slots_nonconstant:
  i.inst_opcode = PHI /\ i.inst_outputs = [out] /\
  i.inst_operands = current_phi_slots ps /\
  FILTER (\v. v <> out) (MAP SND ps) = v::vs /\
  ~EVERY (\w. w = v) vs ==>
  simplify_current_phi i = i
Proof
  strip_tac >>
  `v::vs = FILTER (\v. v <> out) (MAP SND ps)` by simp[] >>
  drule_all current_phi_slots_classify >> simp[]
QED

Theorem current_phi_slots_nop_iff:
  i.inst_opcode = PHI /\ i.inst_outputs = [out] /\
  i.inst_operands = current_phi_slots ps /\
  ns = FILTER (\v. v <> out) (MAP SND ps) ==>
  ((simplify_current_phi i).inst_opcode = NOP <=> ns = [])
Proof
  strip_tac >> drule_all current_phi_slots_classify >>
  disch_then SUBST1_TAC >> Cases_on `ns` >> simp[NoAsms] >>
  IF_CASES_TAC >> gvs[combinTheory.o_DEF,EVERY_MEM,EXISTS_MEM] >> metis_tac[]
QED

Theorem current_phi_slots_assign_iff:
  i.inst_opcode = PHI /\ i.inst_outputs = [out] /\
  i.inst_operands = current_phi_slots ps /\
  ns = FILTER (\v. v <> out) (MAP SND ps) ==>
  ((simplify_current_phi i).inst_opcode = ASSIGN <=>
    ?v vs. ns = v::vs /\ EVERY (\w. w = v) vs)
Proof
  strip_tac >> drule_all current_phi_slots_classify >>
  disch_then SUBST1_TAC >> Cases_on `ns` >> simp[NoAsms] >>
  IF_CASES_TAC >> gvs[combinTheory.o_DEF,EVERY_MEM,EXISTS_MEM] >> metis_tac[]
QED

Theorem current_phi_slots_phi_iff:
  i.inst_opcode = PHI /\ i.inst_outputs = [out] /\
  i.inst_operands = current_phi_slots ps /\
  ns = FILTER (\v. v <> out) (MAP SND ps) ==>
  ((simplify_current_phi i).inst_opcode = PHI <=>
    ?v vs. ns = v::vs /\ ~EVERY (\w. w = v) vs)
Proof
  strip_tac >> drule_all current_phi_slots_classify >>
  disch_then SUBST1_TAC >> Cases_on `ns` >> simp[NoAsms] >>
  IF_CASES_TAC >> gvs[combinTheory.o_DEF,EVERY_MEM,EXISTS_MEM] >> metis_tac[]
QED
