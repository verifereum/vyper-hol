(* Unconditional memory safety transfer, independent of termination. *)
Theory entryMemContinuation
Ancestors
  memSafeRun venomExecSemantics venomInst venomState venomExecProofs

Theorem entry_mem_nonterminator_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK t /\ inst_mem_below_frontier inst s /\
  (!fuel. mem_safe_run fuel ctx fn
    (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !fuel. mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst s = OK t` by simp[step_inst_non_invoke] >>
  drule_all mem_safe_run_step >>
  simp[mem_safe_step_non_invoke]
QED

Theorem entry_mem_terminator_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK t /\ inst_mem_below_frontier inst s /\
  (!fuel. mem_safe_blocks fuel ctx fn t) ==>
  !fuel. mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst s = OK t` by simp[step_inst_non_invoke] >>
  simp[mem_safe_run_def, Once mem_safe_block_def,
       Once exec_block_def, mem_safe_step_non_invoke] >>
  Cases_on `t.vs_halted` >> simp[]
QED

Theorem entry_mem_no_phi_blocks:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
  (!fuel. mem_safe_run fuel ctx fn (s with vs_inst_idx := 0)) ==>
  !fuel. mem_safe_blocks fuel ctx fn s
Proof
  strip_tac >> Cases >- simp[Once mem_safe_blocks_def] >>
  `eval_phis s bb.bb_instructions = OK s` by simp[eval_phis_no_phis] >>
  drule_all mem_safe_blocks_run >>
  simp[no_phis_phi_prefix_length_zero]
QED
