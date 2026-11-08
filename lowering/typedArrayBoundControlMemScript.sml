Theory typedArrayBoundControlMem
Ancestors
  typedArrayLoopControlMem memSafeRun memControlFlow fragExec fragExecMem
  instMemFrontier emitHelperProps exprLoweringProps venomExecSemantics
  venomExecProofs venomState venomInst words arithmetic

(* The bound operand is consumed before either comparison result is written. *)
Theorem typed_array_bound_header_control:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\ i <= n /\ n < dimword(:256) ==>
  exec_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      [mk_inst id LT [Var ctr; bound] [cmp];
       mk_inst (id+1) ISZERO [Var cmp] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|> s =
    OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s))
Proof
  strip_tac >> `i < dimword(:256)` by decide_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, eval_operand_def, lookup_var_update_var,
       w2n_n2w, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       typed_sa_header_state_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `i < n` >>
  simp[bool_to_word_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, jump_to_def, is_terminator_def]
QED

Theorem typed_array_bound_header_mem_safe:
  s.vs_inst_idx = 0 ==>
  mem_safe_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      [mk_inst id LT [Var ctr; bound] [cmp];
       mk_inst (id+1) ISZERO [Var cmp] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|> s
Proof
  strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       is_terminator_def, AllCaseEqs()] >>
  rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       is_terminator_def, AllCaseEqs()] >>
  rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def,
       is_terminator_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem typed_array_bound_header_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      [mk_inst id LT [Var ctr; bound] [cmp];
       mk_inst (id+1) ISZERO [Var cmp] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\ i <= n /\ n < dimword(:256) /\
  lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  mem_cont_sim ctx fn s
    (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s))
Proof
  strip_tac >> irule mem_cont_sim_edge >>
  conj_tac
  >- simp[jump_to_def, typed_sa_header_state_def, update_var_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (goal_assum (drule_at Any) >> conj_tac
      >- (gen_tac >> irule typed_array_bound_header_control >> simp[]) >>
      gen_tac >> irule typed_array_bound_header_mem_safe >> simp[]) >>
  qexists_tac `next_bb` >> simp[jump_to_def]
QED
