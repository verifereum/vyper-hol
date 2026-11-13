Theory fragFuelLoopAbiDecDynSteps
Ancestors
  fragExecMem venomExecSemantics

Theorem abi_dyn_run_from_exit:
  !fn s bb inst r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = r /\
    (!t. r <> OK t) ==>
    !fuel ctx. run_from fuel ctx fn s = r
Proof
  rpt strip_tac >>
  irule (cj 1 fragExecMemTheory.run_from_step_exit) >>
  simp[step_inst_non_invoke]
QED

Theorem abi_dyn_run_from_term:
  !fn s bb inst t fuel ctx.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t ==>
    run_from fuel ctx fn s =
      if t.vs_halted then Halt t else run_blocks fuel ctx fn t
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb s = if t.vs_halted then Halt t else OK t` by
    simp[Once exec_block_def, step_inst_non_invoke] >>
  simp[fragExecTheory.run_from_def] >> Cases_on `t.vs_halted` >> simp[]
QED

Theorem abi_dyn_run_from_term_zero:
  !fn s bb inst t ctx.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t /\ ~t.vs_halted ==>
    run_from 0 ctx fn s = Error "out of fuel"
Proof
  rpt strip_tac >> drule_all abi_dyn_run_from_term >>
  disch_then (qspecl_then [`0`, `ctx`] mp_tac) >>
  simp[Once run_blocks_def]
QED

Theorem abi_dyn_run_from_term_enter:
  !fn s bb inst t tb fuel ctx.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t /\ ~t.vs_halted /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME tb /\
    phi_prefix_length tb.bb_instructions = 0 ==>
    run_from (SUC fuel) ctx fn s =
      run_from fuel ctx fn (t with vs_inst_idx := 0)
Proof
  rpt strip_tac >> drule_all abi_dyn_run_from_term >>
  disch_then (qspecl_then [`SUC fuel`, `ctx`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  irule fragExecTheory.run_blocks_run_from_no_phi >> simp[]
QED
