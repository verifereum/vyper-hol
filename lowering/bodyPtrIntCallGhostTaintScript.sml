Theory bodyPtrIntCallGhostTaint
Ancestors
  ptrSafeRun

Theorem intcall_ghost_taint_mutual:
  (!fuel ctx PG G tn inst s PG' G'.
    SND (ghost_step fuel ctx PG G tn inst s) =
    SND (ghost_step fuel ctx PG' G' tn inst s)) /\
  (!fuel ctx fn PG G tn bb s PG' G'.
    SND (ghost_block fuel ctx fn PG G tn bb s) =
    SND (ghost_block fuel ctx fn PG' G' tn bb s)) /\
  (!fuel ctx fn PG G tn s PG' G'.
    SND (ghost_blocks fuel ctx fn PG G tn s) =
    SND (ghost_blocks fuel ctx fn PG' G' tn s))
Proof
  ho_match_mp_tac ghost_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[ghost_step_def] >>
          Cases_on `decode_invoke inst` >> simp[] >>
          PairCases_on `x` >> simp[] >>
          Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
          Cases_on `eval_operands x1 s` >> simp[] >>
          Cases_on `setup_callee x x' s` >> simp[] >>
          metis_tac[]) >>
      Cases_on `step_inst fuel ctx inst s` >> simp[ghost_step_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `get_instruction bb s.vs_inst_idx`
      >- (simp[SimpRHS, Once ghost_block_def] >> simp[SimpLHS, Once ghost_block_def]) >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      Cases_on `step_inst fuel ctx inst s` >>
      simp[SimpRHS, Once ghost_block_def] >> simp[SimpLHS, Once ghost_block_def] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (Cases_on `v.vs_halted` >> simp[] >> metis_tac[]) >>
      simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `fuel` >- simp[ghost_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[ghost_blocks_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once ghost_blocks_def, Once ghost_blocks_def] >> metis_tac[]
QED

Theorem intcall_ghost_step_taint_prov_independent:
  SND (ghost_step fuel ctx PG G tn inst s) =
  SND (ghost_step fuel ctx PG' G' tn inst s)
Proof
  metis_tac[intcall_ghost_taint_mutual]
QED

Theorem intcall_ghost_block_taint_prov_independent:
  SND (ghost_block fuel ctx fn PG G tn bb s) =
  SND (ghost_block fuel ctx fn PG' G' tn bb s)
Proof
  metis_tac[intcall_ghost_taint_mutual]
QED

Theorem intcall_ghost_blocks_taint_prov_independent:
  SND (ghost_blocks fuel ctx fn PG G tn s) =
  SND (ghost_blocks fuel ctx fn PG' G' tn s)
Proof
  metis_tac[intcall_ghost_taint_mutual]
QED

Theorem intcall_ghost_run_taint_prov_independent:
  SND (ghost_run fuel ctx fn PG G tn s) =
  SND (ghost_run fuel ctx fn PG' G' tn s)
Proof
  simp[ghost_run_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[intcall_ghost_block_taint_prov_independent]
QED
