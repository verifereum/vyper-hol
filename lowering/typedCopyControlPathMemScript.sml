(* Counted memory-safe paths for typed array-loop control. *)
Theory typedCopyControlPathMem
Ancestors
  typedArrayLoopControlMem exprSimBopRestWordLoopPath fragGasSeqMem
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic
  fragGasMode fragExecMem instMemFrontier exprLoweringProps list rich_list memSafeRun

Theorem typed_sa_initial_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  gas_path_mem ctx fn s 0 (OK (jump_to hdr (update_var ctr 0w s)))
Proof
  strip_tac >>
  `gas_marked_path T ctx fn s 0
    (OK (update_var ctr 0w s with vs_inst_idx := LENGTH prefix + 1))` by
    (mp_tac (Q.INST [`code` |-> `[mk_inst id ASSIGN [Lit 0w] [ctr]]`,
                       `t` |-> `update_var ctr 0w s`, `memory` |-> `T`]
                       rest_word_sequence_marked) >>
     simp[] >> disch_then irule >>
     simp[rich_listTheory.DROP_APPEND, IS_PREFIX_APPEND,
          run_inst_seq_def, run_inst_seq_mem_ok_def, mk_inst_def,
          is_terminator_def, step_inst_base_opcode_eqs, exec_pure1_def,
          eval_operand_def, below_frontier_no_ranges,
          inst_dload_in_section_other]) >>
  `gas_marked_path T ctx fn
    (update_var ctr 0w s with vs_inst_idx := LENGTH prefix + 1) 0
    (OK (jump_to hdr (update_var ctr 0w s with vs_inst_idx := LENGTH prefix + 1)))` by
    (irule rest_word_jump_marked >>
     conj_tac >- simp[update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+1) JMP [Label hdr] []`] >>
     simp[update_var_def, get_instruction_def, rich_listTheory.EL_APPEND2,
          mk_inst_def, step_inst_base_opcode_eqs]) >>
  drule_all gas_marked_path_then >> simp[gas_marked_path_def, jump_to_def]
QED

Theorem typed_sa_header_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s)))
Proof
  strip_tac >>
  `gas_marked_path T ctx fn s 0
    (OK (typed_sa_header_state cmp done i ncount s with vs_inst_idx := 2))` by
    (mp_tac (Q.INST
       [`code` |-> `TAKE 2 (typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl)`,
        `t` |-> `typed_sa_header_state cmp done i ncount s`, `memory` |-> `T`,
        `bb` |-> `<|bb_label := hdr; bb_instructions := typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|>`]
       rest_word_sequence_marked) >>
     simp[typed_sa_header_prefix, typed_sa_header_insts_def] >>
     disch_then irule >>
     simp[run_inst_seq_mem_ok_def, mk_inst_def, is_terminator_def,
          step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
          eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, below_frontier_no_ranges]) >>
  `gas_marked_path T ctx fn
    (typed_sa_header_state cmp done i ncount s with vs_inst_idx := 2) 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s with vs_inst_idx := 2)))` by
    (irule rest_word_jump_marked >>
     conj_tac >- simp[typed_sa_header_state_def, update_var_def] >>
     qexistsl_tac
       [`<|bb_label := hdr; bb_instructions := typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|>`,
        `mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []`] >>
     simp[typed_sa_header_state_def, update_var_def, get_instruction_def,
          typed_sa_header_insts_def, mk_inst_def, step_inst_base_opcode_eqs,
          eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `i < ncount` >> simp[bool_to_word_def]) >>
  drule_all gas_marked_path_then >> simp[gas_marked_path_def, jump_to_def]
QED

Theorem typed_sa_backedge_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s)))
Proof
  strip_tac >>
  `gas_marked_path T ctx fn s 0
    (OK (typed_sa_backedge_state ctr nv i s with vs_inst_idx := LENGTH prefix + 2))` by
    (mp_tac (Q.INST
       [`code` |-> `TAKE 2 (typed_sa_backedge_insts id ctr nv hdr)`,
        `t` |-> `typed_sa_backedge_state ctr nv i s`, `memory` |-> `T`]
       rest_word_sequence_marked) >>
     simp[typed_sa_backedge_insts_def] >> disch_then irule >>
     simp[DROP_APPEND, IS_PREFIX_APPEND, run_inst_seq_def,
          run_inst_seq_mem_ok_def, mk_inst_def, is_terminator_def,
          step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
          eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, below_frontier_no_ranges,
          typed_sa_backedge_state_def, GSYM word_add_n2w, ADD1]) >>
  `gas_marked_path T ctx fn
    (typed_sa_backedge_state ctr nv i s with vs_inst_idx := LENGTH prefix + 2) 0
    (OK (jump_to hdr
      (typed_sa_backedge_state ctr nv i s with vs_inst_idx := LENGTH prefix + 2)))` by
    (irule rest_word_jump_marked >>
     conj_tac >- simp[typed_sa_backedge_state_def, update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+2) JMP [Label hdr] []`] >>
     simp[typed_sa_backedge_state_def, update_var_def, get_instruction_def,
          typed_sa_backedge_insts_def, EL_APPEND2, mk_inst_def,
          step_inst_base_opcode_eqs]) >>
  drule_all gas_marked_path_then >> simp[gas_marked_path_def, jump_to_def]
QED
