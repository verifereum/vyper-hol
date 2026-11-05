Theory algebraicOptCmpBlockProofs
Ancestors
  algebraicOptCmpChunkProofs algebraicOptCmpLayoutProofs
  venomExecSemantics venomInst venomState list rich_list

Theorem ao_cmp_get_instruction_drop:
  DROP n bb.bb_instructions = inst::rest ==>
  get_instruction bb n = SOME inst /\
  DROP (SUC n) bb.bb_instructions = rest
Proof
  strip_tac >>
  `n < LENGTH bb.bb_instructions` by
    (Cases_on `n < LENGTH bb.bb_instructions` >> simp[] >>
     gvs[DROP_LENGTH_TOO_LONG]) >>
  gvs[DROP_CONS_EL, get_instruction_def]
QED

Theorem ao_cmp_exec_block_chunk:
  !chunk bb s rest fuel ctx.
  DROP s.vs_inst_idx bb.bb_instructions = chunk ++ rest /\
  EVERY (\i. ~is_terminator i.inst_opcode) chunk ==>
  exec_block fuel ctx bb s =
    case ao_cmp_exec_chunk fuel ctx chunk s of
      OK u => exec_block fuel ctx bb u
    | IntRet vals u => IntRet vals u
    | Halt u => Halt u
    | Abort a u => Abort a u
    | Error e => Error e
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >>
  rpt gen_tac >> strip_tac >>
  drule ao_cmp_get_instruction_drop >> strip_tac >>
  CONV_TAC (LHS_CONV (REWR_CONV (cj 2 run_defs))) >> simp[] >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[ao_cmp_exec_chunk_def] >>
  first_x_assum irule >> simp[]
QED

Theorem ao_cmp_exec_chunk_index:
  !chunk fuel ctx s u.
    ao_cmp_exec_chunk fuel ctx chunk s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH chunk
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >> rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED
