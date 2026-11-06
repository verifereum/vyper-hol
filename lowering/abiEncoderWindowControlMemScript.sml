(* Exact array control endpoints, with instruction-by-instruction memory checks. *)
Theory abiEncoderWindowControlMem
Ancestors
  abiEncoderWindowArrayLoop abiEncoderArrayHeader abiDecoderExecution
  memControlFlow memSafeRun instMemFrontier emitHelperProps venomExecProofs venomExecSemantics
  venomState venomInst words arithmetic list rich_list

Theorem array_header_mem_safe[local]:
  s.vs_inst_idx = 0 /\ eval_operand ip s = SOME p /\
  w2n p + 32 <= s.vs_alloca_next ==>
  mem_safe_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> s
Proof
  strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
    abi_encode_array_header_insts_def, mem_safe_step_def, below_frontier_MLOAD] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
    is_terminator_def] >>
  simp[Once mem_safe_block_def, get_instruction_def,
    abi_encode_array_header_insts_def, mem_safe_step_def,
    below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    is_terminator_def, AllCaseEqs()] >> rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
    abi_encode_array_header_insts_def, mem_safe_step_def,
    below_frontier_no_ranges, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
    is_terminator_def, AllCaseEqs()] >> rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
    abi_encode_array_header_insts_def, mem_safe_step_def,
    below_frontier_no_ranges, mk_inst_def, is_terminator_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem array_header_mem_cont:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w i /\
  i <= n /\ n < dimword (:256) /\ w2n p + 32 <= s.vs_alloca_next ==>
  mem_cont_sim ctx func s
    (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> irule mem_cont_sim_edge >>
  conj_tac >- simp[jump_to_def, abi_encode_array_header_state_def, update_var_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (qexists_tac `<|bb_label := hdr; bb_instructions :=
        abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|>` >>
      simp[] >> conj_tac
      >- (gen_tac >> irule abi_encode_array_header_control >> simp[]) >>
      gen_tac >> irule array_header_mem_safe >> metis_tac[]) >>
  Cases_on `i<n` >> simp[jump_to_def]
QED

Theorem array_backedge_mem_safe[local]:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ w2n p + 32 <= s.vs_alloca_next ==>
  mem_safe_block fuel ctx bb s
Proof
  strip_tac >>
  `SUC (LENGTH prefix) - LENGTH prefix = 1 /\
   SUC (SUC (LENGTH prefix)) - LENGTH prefix = 2` by decide_tac >>
  `!w. eval_operand ip (update_var nv w s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  simp[Once mem_safe_block_def, get_instruction_def, abi_decode_backedge_insts_def,
    rich_listTheory.EL_APPEND2, mem_safe_step_def, below_frontier_no_ranges,
    mk_inst_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    is_terminator_def, AllCaseEqs()] >> rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def, abi_decode_backedge_insts_def,
    rich_listTheory.EL_APPEND2, mem_safe_step_def, below_frontier_MSTORE,
    update_var_def] >>
  simp[step_inst_def, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
    is_terminator_def, AllCaseEqs()] >> rpt strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def, abi_decode_backedge_insts_def,
    rich_listTheory.EL_APPEND2, mem_safe_step_def, below_frontier_no_ranges,
    mk_inst_def, is_terminator_def] >> rpt CASE_TAC >> gvs[update_var_def]
QED

Theorem array_backedge_mem_cont:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword (:256) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  mem_cont_sim ctx func s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >> irule mem_cont_sim_edge >>
  conj_tac >- simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (qexists_tac `bb` >> simp[] >> conj_tac
      >- (gen_tac >> irule abi_decode_backedge_control >> metis_tac[]) >>
      gen_tac >> irule array_backedge_mem_safe >> metis_tac[]) >>
  qexists_tac `hdr_bb` >> simp[jump_to_def]
QED

Theorem window_array_header_run_mem:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w i /\
  i <= n /\ n < dimword (:256) /\ alloca_inv s /\ alloca_room ctx func s /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  window_array_transition ctx func owner ids outs s
    (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s)) /\
  mem_cont_sim ctx func s
    (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> conj_tac
  >- (irule window_array_header_run >> metis_tac[]) >>
  irule array_header_mem_cont >> metis_tac[]
QED

Theorem window_array_backedge_run_mem:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword (:256) /\
  site IN ids /\ FLOOKUP s.vs_allocas site = SOME (w2n p,32) /\
  alloca_inv s /\ alloca_room ctx func s /\
  (!x. not_fresh_at owner x ==> x <> nv) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  window_array_transition ctx func owner ids outs s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))) /\
  mem_cont_sim ctx func s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >> conj_tac
  >- (irule window_array_backedge_run >> metis_tac[]) >>
  irule array_backedge_mem_cont >> metis_tac[]
QED
