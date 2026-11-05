(* Counted finite paths for the membership loop. *)
Theory exprSimBopRestWordLoopPath
Ancestors
  exprSimBopRestWordLayout exprSimBopRestWordLoop exprSimBopRestWordLoadPath
  fragGasMode fragGasPathMem fragGasSeqMem fragGasSeq instMemFrontier gasCount
  memSafeRun venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem rest_word_sequence_marked:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) code /\
  (memory ==> run_inst_seq_mem_ok code s) /\
  run_inst_seq code s = OK t ==>
  gas_marked_path memory ctx fn s 0
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    gvs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    gvs[FILTER_EQ_NIL, EVERY_MEM] >>
  Cases_on `memory` >> gvs[gas_marked_path_def]
  >- (drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  drule_all tuple_run_inst_seq_gas_path >> simp[]
QED

Theorem rest_word_jump_marked:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path memory ctx fn s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `mem_safe_step 0 ctx inst s` by
    (simp[mem_safe_step_non_invoke] >>
     irule below_frontier_no_ranges >> gvs[]) >>
  `gas_path_mem_edge ctx fn s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_mem_edge_def] >> qexists `0:num` >>
     gvs[step_inst_non_invoke, gas_count_step_def, is_terminator_def] >>
     metis_tac[]) >>
  irule gas_marked_path_from_mem >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED

Theorem rest_word_inv_control:
  rest_word_membership_inv idx result len needle elem R i s /\
  (!u lbl. R u ==> R (jump_to lbl u)) /\
  (!u k. R u ==> R (u with vs_inst_idx := k)) ==>
  rest_word_membership_inv idx result len needle elem R i (jump_to lbl s) /\
  rest_word_membership_inv idx result len needle elem R i
    (s with vs_inst_idx := k)
Proof
  simp[rest_word_membership_inv_def, eval_operand_def, lookup_var_def,
       jump_to_def] >> metis_tac[]
QED

Theorem rest_word_layout_caller_path:
  rest_word_loop_layout cs ct fn needle arr len stride off is_in out h code /\
  s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted ==>
  gas_marked_path memory ctx fn s 0 (OK (jump_to h.rw_entry s))
Proof
  simp[rest_word_loop_layout_def] >> rpt strip_tac >>
  irule rest_word_jump_marked >> goal_assum drule >> simp[] >>
  simp[mk_inst_def, step_inst_base_def]
QED

Theorem rest_word_init_sequence:
  run_inst_seq [mk_inst a ASSIGN [Lit 0w] [idx];
                mk_inst b ASSIGN [Lit 0w] [result]] s =
    OK (update_var result 0w (update_var idx 0w s))
Proof
  simp[exprLoweringPropsTheory.run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def]
QED

Theorem rest_word_init_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst a ASSIGN [Lit 0w] [idx];
            mk_inst b ASSIGN [Lit 0w] [result]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_marked_path memory ctx fn s 0
    (OK ((update_var result 0w (update_var idx 0w s)) with
          vs_inst_idx := s.vs_inst_idx + 2))
Proof
  strip_tac >>
  qspec_then `[mk_inst a ASSIGN [Lit 0w] [idx];
               mk_inst b ASSIGN [Lit 0w] [result]]` mp_tac
    (Q.GEN `code` rest_word_sequence_marked) >>
  disch_then (mp_tac o Q.INST [`t` |-> `update_var result 0w (update_var idx 0w s)`]) >>
  simp[rest_word_init_sequence, mk_inst_def, is_terminator_def,
       fragExecMemTheory.run_inst_seq_mem_ok_def] >>
  impl_tac >- (rpt strip_tac >>
    simp[step_inst_base_def, eval_operand_def] >>
    rpt conj_tac >> irule below_frontier_no_ranges >> simp[]) >> simp[]
QED
