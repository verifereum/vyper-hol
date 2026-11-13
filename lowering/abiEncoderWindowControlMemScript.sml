(* Exact array control endpoints, with instruction-by-instruction memory checks. *)
Theory abiEncoderWindowControlMem
Ancestors
  abiEncoderWindowArrayLoop abiEncoderArrayHeader abiDecoderExecution
  memControlFlow memSafeRun instMemFrontier emitHelperProps venomExecProofs venomExecSemantics
  venomState venomInst words arithmetic list rich_list
  fragGasSeqMem fragGasPathMem stmtForRangeMemoryParts

Theorem exec_result_case_only_ok[local]:
  (case r of OK s => P s | Halt v => T | Abort a b => T | IntRet c d => T
   | Error e => T) <=> !s. r = OK s ==> P s
Proof
  Cases_on `r` >> simp[]
QED

Theorem array_header_counted_mem:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w i /\
  i <= n /\ n < dimword (:256) /\ w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s)))
Proof
  strip_tac >> drule_all abi_encode_array_header_prefix >> strip_tac >>
  qabbrev_tac `code = TAKE 3
    (abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl)` >>
  `run_inst_seq code s = OK (abi_encode_array_header_state iv cmp done i n s)` by
    (simp[Abbr `code`] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|>` by simp[] >>
  `run_inst_seq_mem_ok code s` by
    (simp[Abbr `code`, abi_encode_array_header_insts_def,
       Once fragExecMemTheory.run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
     Cases_on `step_inst_base (mk_inst id MLOAD [ip] [iv]) s` >> simp[] >>
     rpt strip_tac >> irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
     simp[] >> rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `EVERY (\x. x.inst_opcode <> INVOKE /\ ~is_terminator x.inst_opcode) code /\
   LENGTH (FILTER (\x. x.inst_opcode = GAS) code) = 0` by
    simp[Abbr `code`, abi_encode_array_header_insts_def, mk_inst_def, is_terminator_def] >>
  `isPREFIX code (DROP s.vs_inst_idx
    (abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl))` by
    simp[Abbr `code`, abi_encode_array_header_insts_def, IS_PREFIX_APPEND] >>
  `gas_path_mem ctx func s (LENGTH (FILTER (\x. x.inst_opcode = GAS) code))
    (OK (abi_encode_array_header_state iv cmp done i n s with
      vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule run_inst_seq_gas_path_mem >> fs[] >>
     simp[Abbr `code`, abi_encode_array_header_insts_def, IS_PREFIX_APPEND]) >>
  qabbrev_tac `middle = abi_encode_array_header_state iv cmp done i n s with vs_inst_idx := 3` >>
  `gas_path_mem ctx func s 0 (OK middle)` by
    gvs[Abbr `middle`, Abbr `code`, abi_encode_array_header_insts_def] >>
  `gas_path_mem ctx func middle 0
    (OK (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s)))` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `bb` |-> `<|bb_label := hdr; bb_instructions :=
         abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|>`,
       `s` |-> `middle`, `op` |-> `Var done`,
       `yes` |-> `exit_lbl`, `no` |-> `body_lbl`, `iid` |-> `id+3`,
       `cond` |-> `bool_to_word (~(i<n))`] (SPEC_ALL for_range_jnz_zero_path_mem)) >>
     simp[Abbr `middle`, abi_encode_array_header_state_def, update_var_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       get_instruction_def, abi_encode_array_header_insts_def] >>
     Cases_on `i<n` >> simp[bool_to_word_def, jump_to_def]) >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

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
  simp[exec_result_case_only_ok]
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
    mk_inst_def, is_terminator_def] >>
  Cases_on `eval_operand (Var iv) s` >>
  simp[eval_operand_def, GSYM update_var_def, lookup_var_update_var] >>
  simp[update_var_def] >> CASE_TAC >> simp[]
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

Theorem array_backedge_counted_mem:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword (:256) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr (mstore (w2n p) (n2w (SUC i))
      (update_var nv (n2w (SUC i)) s))))
Proof
  strip_tac >> drule_all abi_decode_increment_prefix >> strip_tac >>
  `eval_operand ip (update_var nv (n2w (SUC i)) s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `lookup_var iv s = SOME (n2w i)` by fs[eval_operand_def] >>
  qabbrev_tac `code = TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)` >>
  `run_inst_seq code s = OK
    (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))` by
    (simp[Abbr `code`] >> metis_tac[]) >>
  `run_inst_seq_mem_ok code s` by
    (simp[Abbr `code`, abi_decode_backedge_insts_def,
       fragExecMemTheory.run_inst_seq_mem_ok_cons, fragExecMemTheory.run_inst_seq_mem_ok_last,
       memSafeRunTheory.inst_dload_in_section_other, mk_inst_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       word_add_n2w, ADD1, below_frontier_MSTORE, update_var_def] >>
     conj_tac
     >- (irule below_frontier_no_ranges >> simp[]) >>
     simp[GSYM mk_inst_def, below_frontier_MSTORE, GSYM update_var_def, ADD1,
       eval_operand_def, lookup_var_update_var] >> fs[ADD1, update_var_def]) >>
  `EVERY (\x. x.inst_opcode <> INVOKE /\ ~is_terminator x.inst_opcode) code /\
   LENGTH (FILTER (\x. x.inst_opcode = GAS) code) = 0` by
    simp[Abbr `code`, abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `code`, abi_decode_backedge_insts_def, DROP_LENGTH_APPEND, IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qabbrev_tac `middle = mstore (w2n p) (n2w (SUC i))
    (update_var nv (n2w (SUC i)) s) with vs_inst_idx := LENGTH prefix + 2` >>
  `gas_path_mem ctx func s 0 (OK middle)` by
    gvs[Abbr `middle`, Abbr `code`, abi_decode_backedge_insts_def] >>
  suspend "jump"
QED

Resume array_backedge_counted_mem[jump]:
  `gas_path_mem ctx func middle 0 (OK (jump_to hdr middle))` by
    (irule for_range_jump_at_zero_path_mem >>
     (conj_tac >- simp[Abbr `middle`, mstore_def,
       write_memory_with_expansion_def, update_var_def]) >>
     qexistsl_tac [`bb`, `mk_inst (id+2) JMP [Label hdr] []`] >>
     simp[Abbr `middle`, mstore_def, write_memory_with_expansion_def, update_var_def,
       get_instruction_def, abi_decode_backedge_insts_def, EL_APPEND2,
       mk_inst_def, is_terminator_def, memSafeRunTheory.inst_dload_in_section_def,
       step_inst_base_opcode_eqs] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `jump_to hdr middle = jump_to hdr
    (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))` by
    simp[Abbr `middle`, jump_to_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Finalise array_backedge_counted_mem

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
