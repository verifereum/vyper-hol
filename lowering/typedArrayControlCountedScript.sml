(* Counted register-counter control boundaries for typed array traversal. *)
Theory typedArrayControlCounted
Ancestors
  typedArrayLoopControlMem typedCopyLoopCounted bodyMemAssignTopCopyPaths
  fragGasPathMem fragGasSeqMem instMemFrontier fragExecMem fragExec fragGasMode emitHelperProps exprLoweringProps
  venomExecProofs venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem typed_sa_header_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s
        with vs_inst_idx := 2)))
Proof
  strip_tac >>
  drule_all typed_sa_header_prefix >> strip_tac >>
  qabbrev_tac `q = typed_sa_header_state cmp done i ncount s` >>
  `~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `q`, typed_sa_header_state_def, update_var_def] >>
  `gas_marked_path T ctx fn s 0
     (OK (q with vs_inst_idx := s.vs_inst_idx +
       LENGTH (TAKE 2 (typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl))))` by
    (irule topcopy_seq_path >> simp[Abbr `q`] >>
     simp[typed_sa_header_insts_def, mk_inst_def, is_terminator_def,
       IS_PREFIX_APPEND, run_inst_seq_mem_ok_def, below_frontier_no_ranges] >>
     rpt CASE_TAC >> simp[]) >>
  `gas_marked_path T ctx fn (q with vs_inst_idx := 2) 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (q with vs_inst_idx := 2)))` by
    (irule topcopy_jump_path >> simp[] >> qexists
       `mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []` >>
     simp[get_instruction_def, typed_sa_header_insts_def, mk_inst_def,
       step_inst_base_opcode_eqs, Abbr `q`, typed_sa_header_state_def,
       eval_operand_def, lookup_var_update_var] >>
     Cases_on `i < ncount` >> simp[bool_to_word_def]) >>
  gvs[gas_marked_path_def, typed_sa_header_insts_def] >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem typed_sa_backedge_prefix[local]:
  eval_operand (Var ctr) s = SOME (n2w i) ==>
  run_inst_seq (TAKE 2 (typed_sa_backedge_insts id ctr nv hdr)) s =
    OK (typed_sa_backedge_state ctr nv i s)
Proof
  strip_tac >>
  simp[typed_sa_backedge_insts_def, run_inst_seq_def,
    step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, exec_pure1_def,
    eval_operand_def, lookup_var_update_var, typed_sa_backedge_state_def,
    GSYM word_add_n2w, ADD1]
QED

Theorem typed_sa_backedge_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\
  eval_operand (Var ctr) s = SOME (n2w i) ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s
      with vs_inst_idx := LENGTH prefix + 2)))
Proof
  strip_tac >> drule typed_sa_backedge_prefix >> strip_tac >>
  qabbrev_tac `q = typed_sa_backedge_state ctr nv i s` >>
  `~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `q`, typed_sa_backedge_state_def, update_var_def] >>
  `gas_marked_path T ctx fn s 0
    (OK (q with vs_inst_idx := s.vs_inst_idx +
      LENGTH (TAKE 2 (typed_sa_backedge_insts id ctr nv hdr))))` by
    (irule topcopy_seq_path >> simp[Abbr `q`] >>
     simp[typed_sa_backedge_insts_def, mk_inst_def, is_terminator_def,
       DROP_LENGTH_APPEND, IS_PREFIX_APPEND, run_inst_seq_mem_ok_def, below_frontier_no_ranges] >>
     rpt CASE_TAC >> simp[]) >>
  `gas_marked_path T ctx fn (q with vs_inst_idx := LENGTH prefix + 2) 0
    (OK (jump_to hdr (q with vs_inst_idx := LENGTH prefix + 2)))` by
    (irule topcopy_jump_path >> simp[] >>
     qexists `mk_inst (id+2) JMP [Label hdr] []` >>
     simp[get_instruction_def, typed_sa_backedge_insts_def, mk_inst_def,
       step_inst_base_opcode_eqs, EL_APPEND2, Abbr `q`,
       typed_sa_backedge_state_def, update_var_def]) >>
  gvs[gas_marked_path_def, typed_sa_backedge_insts_def] >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem typed_memory_array_condition_prefix[local]:
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword(:256) ==>
  run_inst_seq [mk_inst id1 LT [Var counter; length] [lt];
    mk_inst id2 ISZERO [Var lt] [done]] s =
    OK (typed_sa_header_state lt done i N s)
Proof
  strip_tac >> `i < dimword(:256)` by decide_tac >>
  gvs[eval_operand_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_pure2_def, exec_pure1_def, eval_operand_def, lookup_var_update_var,
    w2n_n2w, typed_sa_header_state_def] >>
  Cases_on `i < N` >> simp[bool_to_word_def]
QED

Theorem typed_memory_array_condition_path_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword(:256) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))
Proof
  strip_tac >> drule_all typed_memory_array_condition_prefix >> strip_tac >>
  qabbrev_tac `q = typed_sa_header_state lt done i N s` >>
  `~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `q`, typed_sa_header_state_def, update_var_def] >>
  `gas_marked_path T ctx func s 0
    (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH
      [mk_inst id1 LT [Var counter; length] [lt];
       mk_inst id2 ISZERO [Var lt] [done]]))` by
    (irule topcopy_seq_path >> simp[Abbr `q`] >>
     simp[mk_inst_def, is_terminator_def, IS_PREFIX_APPEND,
       run_inst_seq_mem_ok_def, below_frontier_no_ranges] >>
     rpt CASE_TAC >> simp[]) >>
  `gas_marked_path T ctx func (q with vs_inst_idx := 2) 0
    (OK (jump_to (if i < N then blabel else exit)
      (q with vs_inst_idx := 2)))` by
    (irule topcopy_jump_path >> simp[] >>
     qexists `mk_inst id3 JNZ [Var done; Label exit; Label blabel] []` >>
     simp[get_instruction_def, mk_inst_def, step_inst_base_opcode_eqs,
       Abbr `q`, typed_sa_header_state_def, eval_operand_def,
       lookup_var_update_var] >>
     Cases_on `i < N` >> simp[bool_to_word_def]) >>
  gvs[gas_marked_path_def, typed_sa_header_state_def] >>
  drule_all gas_path_mem_then >> simp[]
QED
