Theory o1MakeSsaCfg
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps venomInst venomState venomWf list

Theorem rename_current_operands_labels:
  !ops. MAP get_label (rename_current_operands rs ops) = MAP get_label ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def, get_label_def]
QED

Theorem rename_current_inst_successors:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  get_successors inst' = get_successors inst
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >>
  gvs[get_successors_def, rename_current_operands_labels]
QED

Theorem rename_current_block_insts_length:
  !insts s rs rs' s' insts'.
  rename_current_block_insts s rs insts = (rs',s',insts') ==>
  LENGTH insts' = LENGTH insts
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem rename_current_block_insts_last_successors:
  !insts s rs rs' s' insts'.
  insts <> [] /\
  rename_current_block_insts s rs insts = (rs',s',insts') ==>
  get_successors (LAST insts') = get_successors (LAST insts)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `insts = []`
  >- (gvs[rename_current_block_insts_def] >>
      drule rename_current_inst_successors >> simp[]) >>
  `rest' <> []` by
    (drule rename_current_block_insts_length >> Cases_on `rest'` >> gvs[]) >>
  simp[LAST_DEF] >> first_x_assum irule >> metis_tac[]
QED

Theorem rename_current_block_insts_succs:
  rename_current_block_insts s rs bb.bb_instructions = (rs',s',insts') ==>
  bb_succs (bb with bb_instructions := insts') = bb_succs bb
Proof
  strip_tac >>
  drule rename_current_block_insts_length >> strip_tac >>
  Cases_on `bb.bb_instructions = []`
  >- gvs[bb_succs_def] >>
  `insts' <> []` by (Cases_on `insts'` >> gvs[]) >>
  drule_all rename_current_block_insts_last_successors >>
  simp[bb_succs_def] >> Cases_on `bb.bb_instructions` >>
  Cases_on `insts'` >> gvs[]
QED

Theorem update_current_phi_insts_succs:
  bb_succs (bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else inst with inst_operands := update_current_phi_for_pred rs lbl inst.inst_operands)
        bb.bb_instructions) = bb_succs bb
Proof
  qmatch_goalsub_abbrev_tac `MAP f bb.bb_instructions` >>
  Cases_on `bb.bb_instructions` >- simp[bb_succs_def] >>
  simp[bb_succs_def] >>
  pure_once_rewrite_tac[GSYM (CONJUNCT2 MAP)] >>
  simp[LAST_MAP] >>
  Cases_on `(LAST (h::t)).inst_opcode = PHI` >>
  simp[Abbr `f`, get_successors_def, is_terminator_def]
QED
