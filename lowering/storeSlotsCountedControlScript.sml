(* Counted memory-safe control transfers for sparse array stores. *)
Theory storeSlotsCountedControl
Ancestors
  bodyMemAssignTopCopyPaths placeMemoryArrayControl fragGasMode emitHelperProps
  fragExecMem fragGasSeqMem instMemFrontier venomExecProofs venomInstProofs exprLoweringProps
  venomExecSemantics venomState venomInst list rich_list words arithmetic

Theorem store_slots_prefix_jump_mem[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = prefix ++ [term] /\
  s.vs_inst_idx + LENGTH prefix = k /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> GAS) prefix /\
  run_inst_seq_mem_ok prefix s /\ run_inst_seq prefix s = OK u /\
  (term.inst_opcode = JMP \/ term.inst_opcode = JNZ) /\
  step_inst_base term (u with vs_inst_idx := k) =
    OK (jump_to lbl (u with vs_inst_idx := k)) ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to lbl (u with vs_inst_idx := k)))
Proof
  strip_tac >>
  `isPREFIX prefix (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `gas_marked_path T ctx func s 0 (OK (u with vs_inst_idx := k))` by
    (drule_all topcopy_seq_path >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (conj_tac >> irule run_inst_seq_preserves_field >>
     qexists_tac `prefix` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_halted >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  `gas_marked_path T ctx func (u with vs_inst_idx := k) 0
     (OK (jump_to lbl (u with vs_inst_idx := k)))` by
    (irule topcopy_jump_path >> simp[] >> qexists_tac `term` >> simp[] >>
     `DROP k bb.bb_instructions = [term]` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP (LENGTH prefix)`) >>
        pure_rewrite_tac[DROP_DROP_T] >>
        `LENGTH prefix + s.vs_inst_idx = k` by decide_tac >>
        simp[DROP_APPEND]) >>
     `k < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem store_slots_array_init_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []] ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to hdr ((update_var counter 0w s) with
                     vs_inst_idx := s.vs_inst_idx + 1)))
Proof
  strip_tac >> irule store_slots_prefix_jump_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, eval_operand_def, run_inst_seq_mem_ok_last,
       below_frontier_no_ranges]
QED

Theorem store_slots_array_condition_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))
Proof
  strip_tac >>
  irule store_slots_prefix_jump_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var,
       run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last, below_frontier_no_ranges] >>
  `i < dimword (:256)` by decide_tac >>
  gvs[eval_operand_def] >>
  Cases_on `i < N` >> simp[bool_to_word_def, w2n_n2w,
    LESS_MOD, lookup_var_update_var]
QED

Theorem store_slots_array_backedge_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  lookup_var counter s = SOME (n2w i) /\ SUC i < dimword (:256) ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >> irule store_slots_prefix_jump_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, word_add_n2w, ADD1,
       run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last, below_frontier_no_ranges]
QED
