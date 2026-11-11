Theory ctorDeployLoweringFrameDret
Ancestors
  dretDesugarDefs dretDesugarProofs venomInst list

Theorem expand_dret_pairs_opcodes:
  P MCOPY /\ P ADD /\ P AND /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  EVERY (\i. P i.inst_opcode) emitted
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs(), mk_inst_def]
QED

Theorem replace_dret_inst_opcodes:
  EVERY P [MCOPY; ADD; AND; SETFMP; RETFMP] /\
  replace_dret_inst s entry_cursor inst = SOME (replacement,s') ==>
  EVERY (\i. P i.inst_opcode) replacement
Proof
  gvs[replace_dret_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def] >>
  drule_all expand_dret_pairs_opcodes >> simp[]
QED

Theorem dret_desugar_insts_opcodes:
  EVERY P [MCOPY; ADD; AND; SETFMP; RETFMP] /\
  EVERY (\i. P i.inst_opcode) insts /\
  dret_desugar_insts s entry_cursor insts = SOME (out,s') ==>
  EVERY (\i. P i.inst_opcode) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `insts` >> rpt strip_tac >>
  gvs[dret_desugar_insts_def, AllCaseEqs()]
  >- (conj_tac
      >- (irule replace_dret_inst_opcodes >> simp[] >> goal_assum drule) >>
      first_x_assum irule >> goal_assum drule) >>
  first_x_assum irule >> goal_assum drule
QED

Theorem dret_desugar_blocks_opcodes:
  EVERY P [MCOPY; ADD; AND; SETFMP; RETFMP] /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) blocks /\
  dret_desugar_blocks s entry_cursor blocks = SOME (out,s') ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `blocks` >> rpt strip_tac >>
  gvs[dret_desugar_blocks_def, AllCaseEqs()] >>
  conj_tac
  >- (irule dret_desugar_insts_opcodes >> simp[] >> goal_assum drule >> simp[]) >>
  first_x_assum irule >> goal_assum drule
QED

Theorem insert_after_last_param_every_opcode[local]:
  EVERY p insts /\ p new ==>
  EVERY p (insert_after_last_param new insts)
Proof
  Induct_on `insts` >> simp[insert_after_last_param_def] >>
  rpt strip_tac >> Cases_on `EXISTS (\i. is_param_opcode i.inst_opcode) insts` >>
  Cases_on `is_param_opcode h.inst_opcode` >> simp[]
QED

Theorem fn_insts_blocks_every_iff[local]:
  !blocks. EVERY p (fn_insts_blocks blocks) <=>
    EVERY (\bb. EVERY p bb.bb_instructions) blocks
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem dret_desugar_function_opcodes:
  EVERY P [MCOPY; ADD; AND; SETFMP; RETFMP; GETFMP] /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  dret_desugar_function target s fn = SOME (fn',s') ==>
  EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  Cases_on `no_dret fn`
  >- (strip_tac >> gvs[dret_desugar_function_def]) >>
  rpt strip_tac >>
  gvs[dret_desugar_function_def, AllCaseEqs(), fn_insts_def,
      fn_insts_blocks_every_iff] >>
  `EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
     (first'::rest')` by
    (irule dret_desugar_blocks_opcodes >> simp[] >> goal_assum drule >> simp[]) >>
  gvs[] >> irule insert_after_last_param_every_opcode >> simp[mk_inst_def]
QED

Theorem dret_desugar_function_call_free:
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn) /\
  dret_desugar_function target s fn = SOME (fn',s') ==>
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (fn_insts fn')
Proof
  rpt strip_tac >> ho_match_mp_tac dret_desugar_function_opcodes >>
  simp[] >> goal_assum drule >> simp[]
QED
