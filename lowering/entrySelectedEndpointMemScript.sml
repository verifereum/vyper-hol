(* Joint endpoint boundaries for memory-free selected entry control. *)
Theory entrySelectedEndpointMem
Ancestors
  entryDispatchMem memSafeRun venomExecSemantics venomExecProofs
  venomState venomInst instMemFrontier fragExecMem moduleLoweringProps
  emitHelperProps compileEnv moduleLowering stateEquiv fragExec
  exprLoweringProps emitHelper freshWrites

Theorem entry_terminator_endpoint_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK t /\ ~t.vs_halted /\
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
  (!n. mem_safe_blocks n ctx fn t) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >>
  simp[mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def,
       step_inst_non_invoke, mem_safe_step_non_invoke]
QED

Theorem entry_operation_endpoint_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK t /\
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
  (!n. mem_safe_run n ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >>
  `step_inst n ctx inst s = OK t` by simp[step_inst_non_invoke] >>
  drule_all mem_safe_run_step >>
  simp[mem_safe_step_non_invoke]
QED


Theorem entry_jnz_endpoint_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [cond; Label yes; Label no] []) /\
  eval_operand cond s = SOME w /\ ~s.vs_halted ==>
  let t = jump_to (if w <> 0w then yes else no) s in
    vars_pc_only s t /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if w <> 0w then yes else no) /\
    ((!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_run n ctx fn s)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  conj_tac >- simp[vars_pc_only_jump_to, vars_pc_only_refl] >>
  simp[jump_to_def] >> strip_tac >> gen_tac >>
  irule entry_terminator_endpoint_safe >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def,
       step_jnz_behavior, jump_to_def] >>
  conj_tac
  >- (drule step_jnz_behavior >>
      disch_then (qspecl_then [`yes`, `no`, `id`] mp_tac) >>
      Cases_on `w = 0w` >> simp[jump_to_def]) >>
  irule below_frontier_no_ranges >> simp[]
QED
