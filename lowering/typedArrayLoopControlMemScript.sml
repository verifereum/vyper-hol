(* Register-ctr control sequences emitted by compile_copy_sarray_typed. *)
Theory typedArrayLoopControlMem
Ancestors
  memSafeRun memControlFlow fragExec fragExecMem instMemFrontier emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic

Definition typed_sa_header_insts_def:
  typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl =
    [mk_inst id LT [Var ctr; Lit (n2w ncount)] [cmp];
     mk_inst (id+1) ISZERO [Var cmp] [done];
     mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]
End

Definition typed_sa_header_state_def:
  typed_sa_header_state cmp done i ncount s =
    update_var done (bool_to_word (~(i < ncount)))
      (update_var cmp (bool_to_word (i < ncount)) s)
End

Theorem typed_sa_header_prefix:
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) ==>
  run_inst_seq (TAKE 2 (typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl)) s =
    OK (typed_sa_header_state cmp done i ncount s)
Proof
  strip_tac >> `i < dimword(:256)` by decide_tac >>
  simp[typed_sa_header_insts_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       exec_pure1_def, eval_operand_def, lookup_var_update_var,
       w2n_n2w, typed_sa_header_state_def] >>
  Cases_on `i < ncount` >> simp[bool_to_word_def]
QED

Theorem typed_sa_header_control[local]:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) ==>
  exec_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|> s =
    OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s))
Proof
  strip_tac >> `i < dimword(:256)` by decide_tac >>
  simp[Once exec_block_def, get_instruction_def, typed_sa_header_insts_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, typed_sa_header_insts_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, eval_operand_def, lookup_var_update_var,
       w2n_n2w, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, typed_sa_header_insts_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       typed_sa_header_state_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `i < ncount` >>
  simp[bool_to_word_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, jump_to_def, is_terminator_def]

QED

Theorem typed_sa_header_mem_safe[local]:
  s.vs_inst_idx = 0 ==>
  mem_safe_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|> s
Proof
  strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def, typed_sa_header_insts_def,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       is_terminator_def, AllCaseEqs()] >>
  rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def, typed_sa_header_insts_def,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       is_terminator_def, AllCaseEqs()] >>
  rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def, typed_sa_header_insts_def,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def,
       is_terminator_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem typed_sa_header_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) /\
  lookup_block (if i < ncount then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  mem_cont_sim ctx fn s
    (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s))
Proof
  strip_tac >> irule mem_cont_sim_edge >>
  conj_tac
  >- simp[jump_to_def, typed_sa_header_state_def, update_var_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (goal_assum (drule_at Any) >> conj_tac
      >- (gen_tac >> irule typed_sa_header_control >> simp[]) >>
      gen_tac >> irule typed_sa_header_mem_safe >> simp[]) >>
  qexists_tac `next_bb` >> simp[jump_to_def]

QED

Definition typed_sa_backedge_insts_def:
  typed_sa_backedge_insts id ctr nv hdr =
    [mk_inst id ADD [Var ctr; Lit 1w] [nv];
     mk_inst (id+1) ASSIGN [Var nv] [ctr];
     mk_inst (id+2) JMP [Label hdr] []]
End

Definition typed_sa_backedge_state_def:
  typed_sa_backedge_state ctr nv i s =
    update_var ctr (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)
End

Theorem typed_sa_backedge_control[local]:
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) ==>
  exec_block fuel ctx bb s =
    OK (jump_to hdr (typed_sa_backedge_state ctr nv i s))
Proof
  strip_tac >> `i < dimword(:256)` by decide_tac >>
  `n2w i + 1w = (n2w (SUC i):256 word)` by
    simp[GSYM word_add_n2w, arithmeticTheory.ADD1] >>
  `SUC (LENGTH prefix) - LENGTH prefix = 1 /\
   SUC (SUC (LENGTH prefix)) - LENGTH prefix = 2` by decide_tac >>
  simp[Once exec_block_def, get_instruction_def, typed_sa_backedge_insts_def,
       rich_listTheory.EL_APPEND2] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, typed_sa_backedge_insts_def,
       rich_listTheory.EL_APPEND2] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, eval_operand_def, lookup_var_update_var,
       is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, typed_sa_backedge_insts_def,
       rich_listTheory.EL_APPEND2] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       typed_sa_backedge_state_def, jump_to_def, update_var_def,
       is_terminator_def]
QED

Theorem typed_sa_backedge_mem_safe[local]:
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix ==>
  mem_safe_block fuel ctx bb s
Proof
  strip_tac >>
  `SUC (LENGTH prefix) - LENGTH prefix = 1 /\
   SUC (SUC (LENGTH prefix)) - LENGTH prefix = 2` by decide_tac >>
  simp[Once mem_safe_block_def, get_instruction_def, typed_sa_backedge_insts_def,
       rich_listTheory.EL_APPEND2, mem_safe_step_def, below_frontier_no_ranges,
       mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, typed_sa_backedge_insts_def,
       rich_listTheory.EL_APPEND2, mem_safe_step_def, below_frontier_no_ranges,
       mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, typed_sa_backedge_insts_def,
       rich_listTheory.EL_APPEND2, mem_safe_step_def, below_frontier_no_ranges,
       mk_inst_def, is_terminator_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem typed_sa_backedge_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  mem_cont_sim ctx fn s (jump_to hdr (typed_sa_backedge_state ctr nv i s))
Proof
  strip_tac >> irule mem_cont_sim_edge >>
  conj_tac
  >- simp[jump_to_def, typed_sa_backedge_state_def, update_var_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (qexists_tac `bb` >> simp[] >> conj_tac
      >- (gen_tac >> irule typed_sa_backedge_control >> simp[] >>
          conj_tac >- (qexists_tac `ncount` >> simp[]) >>
          qexistsl_tac [`id`, `prefix`] >> simp[]) >>
      metis_tac[typed_sa_backedge_mem_safe]) >>
  qexists_tac `next_bb` >> simp[jump_to_def]
QED

Theorem typed_sa_header_frame:
  (typed_sa_header_state cmp done i ncount s with vs_vars := s.vs_vars) = s /\
  (!x. x <> cmp /\ x <> done ==>
    lookup_var x (typed_sa_header_state cmp done i ncount s) = lookup_var x s)
Proof
  simp[typed_sa_header_state_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem typed_sa_backedge_frame:
  (typed_sa_backedge_state ctr nv i s with vs_vars := s.vs_vars) = s /\
  lookup_var ctr (typed_sa_backedge_state ctr nv i s) = SOME (n2w (SUC i)) /\
  (!x. x <> ctr /\ x <> nv ==>
    lookup_var x (typed_sa_backedge_state ctr nv i s) = lookup_var x s)
Proof
  simp[typed_sa_backedge_state_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem typed_sa_initial_exec[local]:
  bb.bb_instructions = prefix ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  exec_block fuel ctx bb s = OK (jump_to hdr (update_var ctr 0w s)) /\
  mem_safe_block fuel ctx bb s
Proof
  strip_tac >> `SUC (LENGTH prefix) - LENGTH prefix = 1` by decide_tac >>
  conj_tac
  >- (simp[Once exec_block_def, get_instruction_def, rich_listTheory.EL_APPEND2] >>
      simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
           exec_pure1_def, eval_operand_def, is_terminator_def] >>
      simp[Once exec_block_def, get_instruction_def, rich_listTheory.EL_APPEND2] >>
      simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
           eval_operand_def, is_terminator_def, jump_to_def, update_var_def]) >>
  simp[Once mem_safe_block_def, get_instruction_def, rich_listTheory.EL_APPEND2,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       eval_operand_def, is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, rich_listTheory.EL_APPEND2,
       mem_safe_step_def, below_frontier_no_ranges, mk_inst_def, is_terminator_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem typed_sa_initial_sim:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  mem_cont_sim ctx fn s (jump_to hdr (update_var ctr 0w s))
Proof
  strip_tac >> irule mem_cont_sim_edge >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (qexists_tac `bb` >> simp[] >>
      metis_tac[typed_sa_initial_exec]) >>
  qexists_tac `next_bb` >> simp[jump_to_def]
QED
