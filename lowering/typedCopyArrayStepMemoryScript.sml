(* Memory-safe execution of the typed-copy array increment and backedge. *)
Theory typedCopyArrayStepMemory
Ancestors
  typedCopyLoopPathMemory typedMemoryCopy
  stmtForRangeMemoryParts fragGasSeqMem fragGasPathMem fragExecMem
  exprLoweringProps venomExecSemantics venomInst venomState instMemFrontier
  words list rich_list finite_map arithmetic memSafeRun

Theorem typed_copy_backedge_path_mem:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
     mk_inst (id+1) ASSIGN [Var tmp] [ctr];
     mk_inst (id+2) JMP [Label header] []] /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  lookup_var ctr s = SOME (n2w k) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to header (update_var ctr (n2w (k+1))
      (update_var tmp (n2w (k+1)) s))))
Proof
  strip_tac >>
  qabbrev_tac `code = [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
    mk_inst (id+1) ASSIGN [Var tmp] [ctr]]` >>
  qabbrev_tac `u = update_var ctr (n2w (k+1))
    (update_var tmp (n2w (k+1)) s)` >>
  `run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s` by
    simp[Abbr `code`, Abbr `u`, run_inst_seq_def, run_inst_seq_mem_ok_def,
      step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      word_add_n2w, inst_dload_in_section_def, below_frontier_no_ranges,
      mk_inst_def] >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH pre + 2))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def, DROP_LENGTH_APPEND]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := LENGTH pre + 2) 0
    (OK (jump_to header (u with vs_inst_idx := LENGTH pre + 2)))` by
    (irule for_range_jump_at_zero_path_mem >>
     conj_tac >- simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+2) JMP [Label header] []`] >>
     simp[Abbr `u`, update_var_def, get_instruction_def, EL_APPEND_EQN,
       mk_inst_def, is_terminator_def, below_frontier_no_ranges,
       inst_dload_in_section_def, step_inst_base_opcode_eqs]) >>
  `jump_to header (u with vs_inst_idx := LENGTH pre + 2) = jump_to header u` by
    simp[jump_to_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Theorem typed_copy_array_addresses_run:
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so; doff; sp; dp]) /\
  (!x. MEM x [so; doff; sp; dp] ==> ~not_fresh_at sa x) /\
  lookup_var ctr s = SOME (n2w k) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  let code =
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var doff] [dp]];
      u = update_var dp (dw + n2w (k * ds))
        (update_var sp (sw + n2w (k * ss))
          (update_var doff (n2w (k * ds)) (update_var so (n2w (k * ss)) s))) in
  run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s /\
  typed_copy_state_frame sa off len s u /\
  u.vs_memory = s.vs_memory /\
  lookup_var ctr u = SOME (n2w k) /\
  eval_operand (Var sp) u = SOME (sw + n2w (k * ss)) /\
  eval_operand (Var dp) u = SOME (dw + n2w (k * ds))
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> so /\ x <> doff /\ x <> sp /\ x <> dp` by
    (gvs[] >> metis_tac[]) >>
  Cases_on `src` >> Cases_on `dst` >>
  gvs[eval_operand_def, ALL_DISTINCT, MEM, lookup_var_def] >>
  simp[LET_THM, run_inst_seq_def, run_inst_seq_mem_ok_def,
    step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    word_mul_n2w, inst_dload_in_section_def, below_frontier_no_ranges,
    mk_inst_def] >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    venom_state_component_equality]
QED

Theorem typed_copy_array_addresses_path_mem:
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so; doff; sp; dp]) /\
  (!x. MEM x [so; doff; sp; dp] ==> ~not_fresh_at sa x) /\
  lookup_var ctr s = SOME (n2w k) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var doff] [dp]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_state_frame sa off len s t /\ t.vs_memory = s.vs_memory /\
    lookup_var ctr t = SOME (n2w k) /\
    eval_operand (Var sp) t = SOME (sw + n2w (k * ss)) /\
    eval_operand (Var dp) t = SOME (dw + n2w (k * ds)) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + 4 /\ ~t.vs_halted
Proof
  strip_tac >>
  qabbrev_tac `code =
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var doff] [dp]]` >>
  qabbrev_tac `u = update_var dp (dw + n2w (k * ds))
    (update_var sp (sw + n2w (k * ss))
      (update_var doff (n2w (k * ds)) (update_var so (n2w (k * ss)) s)))` >>
  `run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s /\
   typed_copy_state_frame sa off len s u /\ u.vs_memory = s.vs_memory /\
   lookup_var ctr u = SOME (n2w k) /\
   eval_operand (Var sp) u = SOME (sw + n2w (k * ss)) /\
   eval_operand (Var dp) u = SOME (dw + n2w (k * ds))` by
    (unabbrev_all_tac >>
     mp_tac (SRULE [LET_THM] typed_copy_array_addresses_run) >>
     (impl_tac >- (gvs[ALL_DISTINCT, MEM] >> metis_tac[])) >> disch_then ACCEPT_TAC) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := s.vs_inst_idx + 4))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  qexists_tac `u with vs_inst_idx := s.vs_inst_idx + 4` >>
  gvs[eval_operand_def, lookup_var_def, typed_copy_state_frame_def] >>
  simp[Abbr `u`, update_var_def]
QED
