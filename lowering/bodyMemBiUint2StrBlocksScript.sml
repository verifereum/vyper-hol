(* Memory checks for the concrete uint2str instruction templates. *)
Theory bodyMemBiUint2StrBlocks
Ancestors
  bodyMemBiUint2StrBounds exprSimUint2Str fragExecMem instMemFrontier
  memSafeRun venomInst venomState finite_map list rich_list
  venomExecSemantics exprLoweringProps exprSimBopRestWordLoopPath
  fragGasMode fragGasPathMem allocaHistoryFragment

Theorem u2s_body_nonstore_mem_ok[local]:
  run_inst_seq_mem_ok (TAKE 4 (u2s_body a buf n)) s /\
  run_inst_seq_mem_ok (TAKE 4 (DROP 5 (u2s_body a buf n))) s
Proof
  conj_tac >> irule run_inst_seq_mem_ok_every >>
  simp[u2s_body_def, u2s_inst_def] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[inst_dload_in_section_def, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem u2s_body_mem_ok[local]:
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw + n2w n - iw) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 9 (u2s_body a buf n)) s
Proof
  strip_tac >>
  `TAKE 9 (u2s_body a buf n) = TAKE 4 (u2s_body a buf n) ++
    TAKE 5 (DROP 4 (u2s_body a buf n))` by simp[u2s_body_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_body_nonstore_mem_ok] >> rpt strip_tac >>
  drule_all u2s_body_address_run >> strip_tac >> gvs[] >>
  `TAKE 5 (DROP 4 (u2s_body a buf n)) =
    [EL 4 (u2s_body a buf n)] ++ TAKE 4 (DROP 5 (u2s_body a buf n))` by
    simp[u2s_body_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_body_nonstore_mem_ok, run_inst_seq_mem_ok_last,
       u2s_body_def, u2s_inst_def, below_frontier_MSTORE,
       inst_dload_in_section_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[mk_inst_def]
QED

Theorem u2s_final_address_run[local]:
  eval_operand buf s = SOME bw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  (!z. buf = Var z ==> not_fresh_at a z) ==>
  run_inst_seq (TAKE 2 (u2s_final a buf n)) s =
    OK (update_var (u2s_var a 15) (bw+n2w n-iw)
      (update_var (u2s_var a 14) (bw+n2w n) s))
Proof
  strip_tac >>
  simp[u2s_final_def, u2s_inst_def, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem u2s_final_nonstore_mem_ok[local]:
  run_inst_seq_mem_ok (TAKE 2 (u2s_final a buf n)) s /\
  run_inst_seq_mem_ok (TAKE 1 (DROP 3 (u2s_final a buf n))) s
Proof
  conj_tac >> irule run_inst_seq_mem_ok_every >>
  simp[u2s_final_def, u2s_inst_def] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[inst_dload_in_section_def, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem u2s_final_mem_ok[local]:
  eval_operand buf s = SOME bw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw + n2w n - iw) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 4 (u2s_final a buf n)) s
Proof
  strip_tac >>
  `TAKE 4 (u2s_final a buf n) = TAKE 2 (u2s_final a buf n) ++
    TAKE 2 (DROP 2 (u2s_final a buf n))` by simp[u2s_final_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_final_nonstore_mem_ok] >> rpt strip_tac >>
  drule_all u2s_final_address_run >> strip_tac >> gvs[] >>
  `TAKE 2 (DROP 2 (u2s_final a buf n)) =
    [EL 2 (u2s_final a buf n)] ++ TAKE 1 (DROP 3 (u2s_final a buf n))` by
    simp[u2s_final_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_final_nonstore_mem_ok, run_inst_seq_mem_ok_last,
       u2s_final_def, u2s_inst_def, below_frontier_MSTORE,
       inst_dload_in_section_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[mk_inst_def]
QED

Theorem u2s_zero_nonstore_mem_ok[local]:
  run_inst_seq_mem_ok (TAKE 1 (u2s_zero a buf n)) s /\
  run_inst_seq_mem_ok (TAKE 2 (DROP 2 (u2s_zero a buf n))) s /\
  run_inst_seq_mem_ok (TAKE 1 (DROP 5 (u2s_zero a buf n))) s
Proof
  rpt conj_tac >> irule run_inst_seq_mem_ok_every >>
  simp[u2s_zero_def, u2s_inst_def] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[inst_dload_in_section_def, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem u2s_zero_second_address_run[local]:
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) ==>
  run_inst_seq (TAKE 2 (DROP 2 (u2s_zero a buf n))) s =
    OK (update_var (u2s_var a 13) (bw+n2w n-1w)
      (update_var (u2s_var a 12) (bw+n2w n) s))
Proof
  strip_tac >>
  simp[u2s_zero_def, u2s_inst_def, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem u2s_zero_tail_mem_ok[local]:
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw+n2w n-1w) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 4 (DROP 2 (u2s_zero a buf n))) s
Proof
  strip_tac >>
  `TAKE 4 (DROP 2 (u2s_zero a buf n)) =
    TAKE 2 (DROP 2 (u2s_zero a buf n)) ++ TAKE 2 (DROP 4 (u2s_zero a buf n))` by
    simp[u2s_zero_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_zero_nonstore_mem_ok] >> rpt strip_tac >>
  drule_all u2s_zero_second_address_run >> strip_tac >> gvs[] >>
  `TAKE 2 (DROP 4 (u2s_zero a buf n)) =
    [EL 4 (u2s_zero a buf n)] ++ TAKE 1 (DROP 5 (u2s_zero a buf n))` by
    simp[u2s_zero_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_zero_nonstore_mem_ok, run_inst_seq_mem_ok_last,
       u2s_zero_def, u2s_inst_def, below_frontier_MSTORE,
       inst_dload_in_section_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[mk_inst_def]
QED

Theorem u2s_zero_first_address_run[local]:
  eval_operand buf s = SOME bw ==>
  run_inst_seq (TAKE 1 (u2s_zero a buf n)) s =
    OK (update_var (u2s_var a 11) (bw+n2w n) s)
Proof
  strip_tac >>
  simp[u2s_zero_def, u2s_inst_def, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operands_def, eval_operand_def]
QED

Theorem u2s_zero_mem_ok[local]:
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw+n2w n) + 32 <= s.vs_alloca_next /\
  w2n (bw+n2w n-1w) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 6 (u2s_zero a buf n)) s
Proof
  strip_tac >>
  `TAKE 6 (u2s_zero a buf n) = TAKE 1 (u2s_zero a buf n) ++
    TAKE 5 (DROP 1 (u2s_zero a buf n))` by simp[u2s_zero_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_zero_nonstore_mem_ok] >> rpt strip_tac >>
  drule u2s_zero_first_address_run >> strip_tac >> gvs[] >>
  `TAKE 5 (DROP 1 (u2s_zero a buf n)) =
    [EL 1 (u2s_zero a buf n)] ++ TAKE 4 (DROP 2 (u2s_zero a buf n))` by
    simp[u2s_zero_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (simp[run_inst_seq_mem_ok_last, u2s_zero_def, u2s_inst_def,
           below_frontier_MSTORE, inst_dload_in_section_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      simp[mk_inst_def]) >>
  rpt strip_tac >> irule u2s_zero_tail_mem_ok >>
  conj_tac >- simp[] >> qexists_tac `bw` >>
  qpat_x_assum `run_inst_seq [_] _ = _` mp_tac >>
  simp[u2s_zero_def, u2s_inst_def, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operands_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `buf` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rename1 `not_fresh_at a z` >>
  `z <> u2s_var a 11` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def, u2s_var_def,
         compileEnvTheory.fresh_var_def]) >> simp[]
QED

Theorem u2s_drop_prefix[local]:
  !pre code j. DROP (LENGTH pre) (pre ++ code ++ [j]) = code ++ [j]
Proof
  Induct >> simp[]
QED

Theorem u2s_memory_block_path[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ code ++ [j] /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\
  run_inst_seq code s = OK t /\ ~t.vs_halted /\
  t.vs_current_bb = s.vs_current_bb /\
  (j.inst_opcode = JMP \/ j.inst_opcode = JNZ) /\
  step_inst_base j (t with vs_inst_idx := LENGTH pre + LENGTH code) =
    OK (jump_to lbl (t with vs_inst_idx := LENGTH pre + LENGTH code)) ==>
  gas_path_mem ctx fn s 0 (OK (jump_to lbl t))
Proof
  strip_tac >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (simp[u2s_drop_prefix, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `gas_marked_path T ctx fn s 0
    (OK (t with vs_inst_idx := LENGTH pre + LENGTH code))` by
    (qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac [GSYM th]) >>
     irule rest_word_sequence_marked >>
     simp[u2s_drop_prefix, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `gas_marked_path T ctx fn (t with vs_inst_idx := LENGTH pre + LENGTH code)
    0 (OK (jump_to lbl (t with vs_inst_idx := LENGTH pre + LENGTH code)))` by
    (irule rest_word_jump_marked >> simp[] >>
     qexists_tac `j` >>
     simp[get_instruction_def, EL_APPEND_EQN, arithmeticTheory.ADD_COMM] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_all gas_marked_path_then >>
  simp[gas_marked_path_def, jump_to_def]
QED

Theorem u2s_sequence_alloca_fields[local]:
  run_inst_seq code s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> conj_tac >>
  irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  gvs[EVERY_MEM] >>
  metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_fields]
QED

Theorem u2s_block_history[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ code ++ [j] /\
  s.vs_inst_idx = LENGTH pre /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> ALLOCA) code /\
  run_inst_seq code s = OK t ==>
  alloca_history fn (jump_to lbl t) /\
  (jump_to lbl t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by gvs[EVERY_MEM] >>
  `alloca_history fn (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)` by
    (irule alloca_history_run_inst_seq >>
     goal_assum (drule_at Any) >> simp[u2s_drop_prefix] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule u2s_sequence_alloca_fields >> goal_assum (drule_at Any) >>
     gvs[EVERY_MEM]) >>
  reverse conj_tac >- simp[jump_to_def] >>
  irule allocaHistoryTheory.alloca_history_jump >> simp[jump_to_def] >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  simp[jump_to_def]
QED

Theorem u2s_memory_block_history[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ code ++ [j] /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS /\ i.inst_opcode <> ALLOCA) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
  (j.inst_opcode = JMP \/ j.inst_opcode = JNZ) /\
  step_inst_base j (t with vs_inst_idx := LENGTH pre + LENGTH code) =
    OK (jump_to lbl (t with vs_inst_idx := LENGTH pre + LENGTH code)) ==>
  gas_path_mem ctx fn s 0 (OK (jump_to lbl t)) /\
  alloca_history fn (jump_to lbl t) /\
  (jump_to lbl t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> (conj_tac
  >- (irule u2s_memory_block_path >> goal_assum (drule_at Any) >>
      simp[] >> qexistsl_tac [`code`, `pre`] >> gvs[EVERY_MEM] >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> ALLOCA) code` by gvs[EVERY_MEM] >>
  drule_all u2s_block_history >> simp[])
QED

Theorem u2s_body_memory_path:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw+n2w n-iw)+32 <= s.vs_alloca_next /\
  run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb ==>
  gas_path_mem ctx fn s 0 (OK (jump_to (u2s_label a 1) t)) /\
  alloca_history fn (jump_to (u2s_label a 1) t) /\
  (jump_to (u2s_label a 1) t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (TAKE 9 (u2s_body a buf n)) s` by
    (irule u2s_body_mem_ok >> metis_tac[]) >>
  match_mp_tac (Q.INST
    [`bb` |-> `<|bb_label := u2s_label a 2;
                 bb_instructions := u2s_body a buf n|>`,
     `pre` |-> `[]`, `code` |-> `TAKE 9 (u2s_body a buf n)`,
     `j` |-> `LAST (u2s_body a buf n)`] u2s_memory_block_history) >>
  simp[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def,
       step_inst_base_def]
QED

Theorem u2s_final_memory_path:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw+n2w n-iw)+32 <= s.vs_alloca_next /\
  run_inst_seq (TAKE 4 (u2s_final a buf n)) s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb ==>
  gas_path_mem ctx fn s 0 (OK (jump_to (u2s_label a 5) t)) /\
  alloca_history fn (jump_to (u2s_label a 5) t) /\
  (jump_to (u2s_label a 5) t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (TAKE 4 (u2s_final a buf n)) s` by
    (irule u2s_final_mem_ok >> metis_tac[]) >>
  match_mp_tac (Q.INST
    [`bb` |-> `<|bb_label := u2s_label a 4;
                 bb_instructions := u2s_final a buf n|>`,
     `pre` |-> `[]`, `code` |-> `TAKE 4 (u2s_final a buf n)`,
     `j` |-> `LAST (u2s_final a buf n)`] u2s_memory_block_history) >>
  simp[u2s_final_def, u2s_inst_def, mk_inst_def, is_terminator_def,
       step_inst_base_def]
QED

Theorem u2s_zero_memory_path:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw+n2w n)+32 <= s.vs_alloca_next /\
  w2n (bw+n2w n-1w)+32 <= s.vs_alloca_next /\
  run_inst_seq (TAKE 6 (u2s_zero a buf n)) s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb ==>
  gas_path_mem ctx fn s 0 (OK (jump_to (u2s_label a 5) t)) /\
  alloca_history fn (jump_to (u2s_label a 5) t) /\
  (jump_to (u2s_label a 5) t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (TAKE 6 (u2s_zero a buf n)) s` by
    (irule u2s_zero_mem_ok >> metis_tac[]) >>
  match_mp_tac (Q.INST
    [`bb` |-> `<|bb_label := u2s_label a 3;
                 bb_instructions := u2s_zero a buf n|>`,
     `pre` |-> `[]`, `code` |-> `TAKE 6 (u2s_zero a buf n)`,
     `j` |-> `LAST (u2s_zero a buf n)`] u2s_memory_block_history) >>
  simp[u2s_zero_def, u2s_inst_def, mk_inst_def, is_terminator_def,
       step_inst_base_def]
QED

Theorem u2s_setup_memory_path:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op buf /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  run_inst_seq (TAKE 3 (u2s_setup a op buf)) s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb ==>
  gas_path_mem ctx fn s 0 (OK (jump_to (u2s_label a 0) t)) /\
  alloca_history fn (jump_to (u2s_label a 0) t) /\
  (jump_to (u2s_label a 0) t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (TAKE 3 (u2s_setup a op buf)) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[u2s_setup_def, u2s_inst_def] >>
     rpt conj_tac >> rpt gen_tac >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  match_mp_tac (Q.INST
    [`bb` |-> `bb`, `pre` |-> `pre`,
     `code` |-> `TAKE 3 (u2s_setup a op buf)`,
     `j` |-> `LAST (u2s_setup a op buf)`] u2s_memory_block_history) >>
  simp[u2s_setup_def, u2s_inst_def, mk_inst_def, is_terminator_def,
       step_inst_base_def]
QED

Theorem u2s_check_memory_path:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  run_inst_seq (TAKE 1 (u2s_check a)) s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
  step_inst_base (LAST (u2s_check a)) (t with vs_inst_idx := 1) =
    OK (jump_to lbl (t with vs_inst_idx := 1)) ==>
  gas_path_mem ctx fn s 0 (OK (jump_to lbl t)) /\
  alloca_history fn (jump_to lbl t) /\
  (jump_to lbl t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (TAKE 1 (u2s_check a)) s` by
    (irule run_inst_seq_mem_ok_every >> simp[u2s_check_def, u2s_inst_def] >>
     rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  match_mp_tac (Q.INST
    [`bb` |-> `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>`,
     `pre` |-> `[]`, `code` |-> `TAKE 1 (u2s_check a)`,
     `j` |-> `LAST (u2s_check a)`] u2s_memory_block_history) >>
  gvs[u2s_check_def, u2s_inst_def, mk_inst_def, is_terminator_def]
QED

Theorem u2s_cond_memory_path:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  run_inst_seq (TAKE 1 (u2s_cond a)) s = OK t /\
  ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
  step_inst_base (LAST (u2s_cond a)) (t with vs_inst_idx := 1) =
    OK (jump_to lbl (t with vs_inst_idx := 1)) ==>
  gas_path_mem ctx fn s 0 (OK (jump_to lbl t)) /\
  alloca_history fn (jump_to lbl t) /\
  (jump_to lbl t).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (TAKE 1 (u2s_cond a)) s` by
    (irule run_inst_seq_mem_ok_every >> simp[u2s_cond_def, u2s_inst_def] >>
     rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  match_mp_tac (Q.INST
    [`bb` |-> `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>`,
     `pre` |-> `[]`, `code` |-> `TAKE 1 (u2s_cond a)`,
     `j` |-> `LAST (u2s_cond a)`] u2s_memory_block_history) >>
  gvs[u2s_cond_def, u2s_inst_def, mk_inst_def, is_terminator_def]
QED
