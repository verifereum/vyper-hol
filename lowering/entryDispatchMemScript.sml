(* Continuation boundaries for memory-free entry control flow. *)
Theory entryDispatchMem
Ancestors
  memSafeRun venomExecSemantics venomExecProofs venomState venomInst
  instMemFrontier fragExecMem list

Theorem mem_safe_run_terminator_intro[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ mem_safe_step fuel ctx inst s /\
  (!t. step_inst fuel ctx inst s = OK t /\ ~t.vs_halted ==>
       mem_safe_blocks fuel ctx fn t) ==>
  mem_safe_run fuel ctx fn s
Proof
  strip_tac >> simp[mem_safe_run_def, Once mem_safe_block_def,
    Once exec_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `OK t` >> Cases_on `t.vs_halted` >> simp[]
QED

Theorem mem_safe_blocks_no_phi[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK s /\
  phi_prefix_length bb.bb_instructions = 0 /\
  (!n. mem_safe_run n ctx fn (s with vs_inst_idx := 0)) ==>
  !n. mem_safe_blocks n ctx fn s
Proof
  strip_tac >> Cases
  >- simp[Once mem_safe_blocks_def] >>
  drule_all mem_safe_blocks_run >> simp[]
QED

Theorem mem_safe_run_jmp[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  (!n. mem_safe_blocks n ctx fn (jump_to lbl s)) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >> irule mem_safe_run_terminator_intro >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, mem_safe_step_non_invoke,
    step_inst_non_invoke, step_jmp_behavior] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem mem_safe_run_jnz[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [cond; Label yes; Label no] []) /\
  eval_operand cond s = SOME w /\
  (!n. mem_safe_blocks n ctx fn (jump_to (if w <> 0w then yes else no) s)) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >> irule mem_safe_run_terminator_intro >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, mem_safe_step_non_invoke,
    step_inst_non_invoke] >>
  reverse conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_jnz_behavior >> Cases_on `w = 0w` >> gvs[]
QED
