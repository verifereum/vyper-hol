Theory dftPacketFreshCut
Ancestors
  dftPacketEntryReplay dftPacketFreshRow dftRunRel dftIndexedExec
  dftGasToListReplay gasEvents frameGasEvents venomExecSemantics
  venomInst venomState stateEquiv list rich_list arithmetic

Theorem fresh_cut_pseudo_events[local]:
  !pre bb s t.
    EVERY (\i. is_pseudo i.inst_opcode) pre /\
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ rest /\
    FOLDR (dft_exec_cons f C) OK pre s = OK t ==>
    gas_events_block f C owner bb s = gas_events_block f C owner bb t
Proof
  Induct_on `pre` >- simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> GAS /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[LIST_EQ_REWRITE,LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ rest` by
    gvs[DROP_CONS_EL] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  gvs[dft_exec_cons_def,AllCaseEqs()] >>
  rename1 `step_inst f C h s = OK u` >>
  simp[Once gas_events_defs,get_instruction_def,gas_events_step_plain] >>
  first_x_assum irule >> simp[]
QED
