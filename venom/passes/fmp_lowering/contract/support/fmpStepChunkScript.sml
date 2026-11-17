Theory fmpStepChunk
Ancestors
  fmpStepList venomWf list

Theorem bb_well_formed_list:
  bb_well_formed bb <=>
    list_terminal (\i. is_terminator i.inst_opcode) bb.bb_instructions /\
    list_prefix (\i. i.inst_opcode = PHI) bb.bb_instructions
Proof
  simp[bb_well_formed_def, list_terminal_indexed, list_prefix_indexed,
       CONJ_ASSOC]
QED

Theorem bb_well_formed_expand:
  bb_well_formed bb /\
  (!i. MEM i bb.bb_instructions ==> f i <> [] /\
    (if is_terminator i.inst_opcode then
       list_terminal (\j. is_terminator j.inst_opcode) (f i)
     else EVERY (\j. ~is_terminator j.inst_opcode) (f i)) /\
    (if i.inst_opcode = PHI then EVERY (\j. j.inst_opcode = PHI) (f i)
     else EVERY (\j. j.inst_opcode <> PHI) (f i))) ==>
  bb_well_formed (bb with bb_instructions := FLAT (MAP f bb.bb_instructions))
Proof
  rewrite_tac[bb_well_formed_list] >> strip_tac >> simp[] >> conj_tac
  >- (irule list_terminal_expand >> qexists_tac `\i. is_terminator i.inst_opcode` >>
      simp[] >> metis_tac[]) >>
  irule list_prefix_expand >> qexists_tac `\i. i.inst_opcode = PHI` >>
  simp[] >> metis_tac[]
QED

Theorem bb_well_formed_insert:
  bb.bb_instructions = xs ++ ys /\ bb_well_formed bb /\ ys <> [] /\
  EVERY (\i. i.inst_opcode <> PHI) ys /\
  EVERY (\i. i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode) ins ==>
  bb_well_formed (bb with bb_instructions := xs ++ ins ++ ys)
Proof
  rewrite_tac[bb_well_formed_list] >> strip_tac >> simp[] >> conj_tac
  >- (irule list_terminal_insert >> gvs[EVERY_MEM] >> metis_tac[]) >>
  irule list_prefix_insert >> gvs[EVERY_MEM] >> metis_tac[]
QED
