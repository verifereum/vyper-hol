(* Finite memory-safe control paths for typed array normalization. *)
Theory typedArrayLoopPathMem
Ancestors
  typedArrayLoopControlMem fragGasSeqMem instMemFrontier fragGasPathMem gasCount memSafeRun
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic
  emitHelperProps exprLoweringProps

Theorem typed_sa_header_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) /\
  lookup_block (if i < ncount then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s)))
Proof
  strip_tac >> `i < dimword(:256)` by decide_tac >>
  qabbrev_tac `s1 = (update_var cmp (bool_to_word (i < ncount)) s) with vs_inst_idx := 1` >>
  qabbrev_tac `s2 = (update_var done (bool_to_word (~(i < ncount))) s1) with vs_inst_idx := 2` >>
  `gas_path_mem_edge ctx fn s 0 (OK s1)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[get_instruction_def, typed_sa_header_insts_def, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, w2n_n2w, gas_count_step_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges, inst_dload_in_section_def,
       is_terminator_def, Abbr `s1`, update_var_def]) >>
  `gas_path_mem_edge ctx fn s1 0 (OK s2)` by
    (simp[gas_path_mem_edge_def, Abbr `s1`, update_var_def] >> qexists_tac `0` >>
     simp[get_instruction_def, typed_sa_header_insts_def, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       gas_count_step_def, mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, is_terminator_def, Abbr `s2`, update_var_def] >>
     Cases_on `i < ncount` >> simp[bool_to_word_def]) >>
  `gas_path_mem_edge ctx fn s2 0
     (OK (jump_to (if i < ncount then body_lbl else exit_lbl) s2))` by
    (simp[gas_path_mem_edge_def, Abbr `s2`, Abbr `s1`, update_var_def] >>
     qexists_tac `0` >>
     simp[get_instruction_def, typed_sa_header_insts_def, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, gas_count_step_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges, inst_dload_in_section_def,
       is_terminator_def] >>
     Cases_on `i < ncount` >> simp[bool_to_word_def, jump_to_def] >> metis_tac[]) >>
  `jump_to (if i < ncount then body_lbl else exit_lbl) s2 =
   jump_to (if i < ncount then body_lbl else exit_lbl)
     (typed_sa_header_state cmp done i ncount s)` by
    simp[Abbr `s2`, Abbr `s1`, typed_sa_header_state_def, jump_to_def, update_var_def] >>
  `~s2.vs_halted` by simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
  `~(jump_to (if i < ncount then body_lbl else exit_lbl) s2).vs_halted` by simp[jump_to_def, typed_sa_header_state_def, update_var_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED

Theorem typed_sa_backedge_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  gas_path_mem ctx fn s 0 (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s)))
Proof
  strip_tac >>
  `n2w i + 1w = (n2w (SUC i):256 word)` by simp[GSYM word_add_n2w, ADD1] >>
  `SUC (LENGTH prefix) - LENGTH prefix = 1 /\
   SUC (SUC (LENGTH prefix)) - LENGTH prefix = 2` by decide_tac >>
  qabbrev_tac `s1 = (update_var nv (n2w (SUC i)) s) with vs_inst_idx := SUC (LENGTH prefix)` >>
  qabbrev_tac `s2 = (update_var ctr (n2w (SUC i)) s1) with vs_inst_idx := SUC (SUC (LENGTH prefix))` >>
  `gas_path_mem_edge ctx fn s 0 (OK s1)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[get_instruction_def, typed_sa_backedge_insts_def, rich_listTheory.EL_APPEND2,
       mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, gas_count_step_def, mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, is_terminator_def, Abbr `s1`, update_var_def]) >>
  `gas_path_mem_edge ctx fn s1 0 (OK s2)` by
    (simp[gas_path_mem_edge_def, Abbr `s1`, update_var_def] >> qexists_tac `0` >>
     simp[get_instruction_def, typed_sa_backedge_insts_def, rich_listTheory.EL_APPEND2,
       mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       gas_count_step_def, mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, is_terminator_def, Abbr `s2`, update_var_def]) >>
  `gas_path_mem_edge ctx fn s2 0 (OK (jump_to hdr s2))` by
    (simp[gas_path_mem_edge_def, Abbr `s2`, Abbr `s1`, update_var_def] >>
     qexists_tac `0` >>
     simp[get_instruction_def, typed_sa_backedge_insts_def, rich_listTheory.EL_APPEND2,
       mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       gas_count_step_def, mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, is_terminator_def] >> metis_tac[]) >>
  `jump_to hdr s2 = jump_to hdr (typed_sa_backedge_state ctr nv i s)` by
    simp[Abbr `s2`, Abbr `s1`, typed_sa_backedge_state_def, jump_to_def, update_var_def] >>
  `~(jump_to hdr s2).vs_halted` by
    simp[jump_to_def, typed_sa_backedge_state_def, update_var_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
