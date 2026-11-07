Theory lowerDloadPositionBoundary
Ancestors
  o1ContractLowerDload lowerDloadPhaseBoundary list rich_list arithmetic
  venomState venomExecSemantics ptrDiscipline

Theorem ld_target_prefix_position:
  ld_target_prefix C code t0 u0 n t u /\
  out = before ++ code ++ after /\
  t0.vs_inst_idx = LENGTH before /\ n < LENGTH code ==>
  t.vs_inst_idx < LENGTH out /\ EL t.vs_inst_idx out = EL n code
Proof
  strip_tac >> drule ld_target_prefix_index >> strip_tac >>
  gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2, EL_APPEND1]
QED

Theorem ld_target_prefix_completed_position:
  ld_target_prefix C code t0 u0 (LENGTH code) t u /\
  t0.vs_inst_idx = LENGTH before ==>
  t.vs_inst_idx = LENGTH (before ++ code)
Proof
  strip_tac >> drule ld_target_prefix_index >> simp[]
QED

Theorem ld_target_prefix_position_step:
  ld_target_prefix C code t0 u0 n t u /\
  out = before ++ code ++ after /\
  t0.vs_inst_idx = LENGTH before /\ n < LENGTH code /\
  step_inst fuel C (EL t.vs_inst_idx out) t = OK z ==>
  ld_target_prefix C code t0 u0 (SUC n)
    (z with vs_inst_idx := SUC t.vs_inst_idx)
    (step_taint (EL t.vs_inst_idx out) t z u)
Proof
  strip_tac >> drule_all ld_target_prefix_position >> strip_tac >>
  gvs[] >> irule (cj 2 ld_target_prefix_rules) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
