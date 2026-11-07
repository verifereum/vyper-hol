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
    simp[below_frontier_no_ranges] >>
    CASE_TAC >> simp[below_frontier_no_ranges] >>
    CASE_TAC >> simp[]) >> simp[]
QED

Theorem rest_word_block_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = 0 /\ bb.bb_instructions = code ++ [inst] /\
  ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) code /\
  (memory ==> run_inst_seq_mem_ok code s) /\
  run_inst_seq code s = OK u /\ ~u.vs_halted /\
  u.vs_current_bb = s.vs_current_bb /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst (u with vs_inst_idx := LENGTH code) =
    OK (jump_to lbl (u with vs_inst_idx := LENGTH code)) /\
  t = jump_to lbl (u with vs_inst_idx := LENGTH code) ==>
  gas_marked_path memory ctx fn s 0 (OK t)
Proof
  strip_tac >>
  `gas_marked_path memory ctx fn s 0
     (OK (u with vs_inst_idx := LENGTH code))` by
    (mp_tac (Q.INST [`t` |-> `u`] rest_word_sequence_marked) >> simp[]) >>
  `gas_marked_path memory ctx fn (u with vs_inst_idx := LENGTH code) 0 (OK t)` by
    (qpat_x_assum `t = _` SUBST1_TAC >>
     irule rest_word_jump_marked >> simp[] >>
     qexists `inst` >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem rest_word_layout_entry_path:
  rest_word_loop_layout cs ct fn needle arr lenop stride off is_in out h code /\
  s.vs_current_bb = h.rw_entry /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  h.rw_idx <> h.rw_result /\ len < dimword (:256) /\
  R (update_var h.rw_result 0w (update_var h.rw_idx 0w s)) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = h.rw_cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      rest_word_membership_inv h.rw_idx h.rw_result len needleval elem R 0 t
Proof
  strip_tac >> drule rest_word_loop_layout_entry >> strip_tac >>
  qmatch_asmsub_abbrev_tac `R u` >>
  qexists `jump_to h.rw_cond u` >>
  conj_tac
  >- (irule rest_word_block_path >> simp[Once CONJ_ASSOC] >>
      qexistsl [`h.rw_cond`, `u`] >>
      simp[rest_word_init_sequence, Abbr `u`, update_var_def,
           jump_to_def, mk_inst_def, is_terminator_def] >>
      conj_tac
      >- simp[step_inst_base_def, eval_operand_def, jump_to_def] >>
      strip_tac >>
      simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
           below_frontier_no_ranges] >>
      CASE_TAC >> simp[below_frontier_no_ranges] >>
      CASE_TAC >> simp[]) >>
  `R (jump_to h.rw_cond u)` by metis_tac[] >>
  `rest_word_membership_inv h.rw_idx h.rw_result len needleval elem R 0 u` by
    (simp[Abbr `u`] >> irule rest_word_membership_init >> simp[]) >>
  gvs[rest_word_membership_inv_def, jump_to_def, eval_operand_def,
      lookup_var_def, Abbr `u`, update_var_def]
QED

Theorem rest_word_cond_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := label;
      bb_instructions := [mk_inst a EQ [Var idx; lenop] [done];
        mk_inst b JNZ [Var done; Label exit; Label body_lbl] []]|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  rest_word_membership_inv idx result len needle elem R i s /\
  eval_operand lenop s = SOME (n2w len) /\
  done <> idx /\ done <> result /\
  R (update_var done (bool_to_word (i = len)) s) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = (if i = len then exit else body_lbl) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      rest_word_membership_inv idx result len needle elem R i t
Proof
  strip_tac >>
  `step_inst_base (mk_inst a EQ [Var idx; lenop] [done]) s =
     OK (update_var done (bool_to_word (i = len)) s)` by
    (irule rest_word_membership_test >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `R u` >>
  qexists `jump_to (if i = len then exit else body_lbl) u` >> conj_tac
  >- (irule rest_word_block_path >> simp[Once CONJ_ASSOC] >>
      qexistsl [`if i = len then exit else body_lbl`, `u`] >>
      simp[exprLoweringPropsTheory.run_inst_seq_def, is_terminator_def,
           fragExecMemTheory.run_inst_seq_mem_ok_def] >>
      conj_tac
      >- (simp[Abbr `u`, update_var_def]) >>
      conj_tac
      >- (irule rest_word_membership_branch >>
          simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
               FLOOKUP_UPDATE]) >>
      simp[Abbr `u`, update_var_def, jump_to_def] >>
      strip_tac >> irule below_frontier_no_ranges >> simp[]) >>
  `R (jump_to (if i = len then exit else body_lbl) u)` by metis_tac[] >>
  `rest_word_membership_inv idx result len needle elem R i u` by
    (irule rest_word_membership_inv_frame >>
     simp[Abbr `u`, update_var_def, FLOOKUP_UPDATE] >>
     qexists `s` >> simp[]) >>
  gvs[rest_word_membership_inv_def, jump_to_def, eval_operand_def,
      lookup_var_def, Abbr `u`, update_var_def]
QED

Theorem rest_word_found_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := label;
      bb_instructions := [mk_inst a ASSIGN [Lit 1w] [result];
                          mk_inst b JMP [Label exit] []]|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  R (update_var result 1w s) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      eval_operand (Var result) t = SOME 1w /\ R t
Proof
  strip_tac >> qmatch_asmsub_abbrev_tac `R u` >>
  qexists `jump_to exit u` >> conj_tac
  >- (irule rest_word_block_path >> simp[Once CONJ_ASSOC] >>
      qexistsl [`exit`, `u`] >>
      simp[Abbr `u`, update_var_def, jump_to_def, mk_inst_def,
           is_terminator_def] >>
      conj_tac
      >- simp[exprLoweringPropsTheory.run_inst_seq_def,
              step_inst_base_def, eval_operand_def, update_var_def] >>
      conj_tac
      >- simp[step_inst_base_def, eval_operand_def, jump_to_def] >>
      strip_tac >>
      simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
           below_frontier_no_ranges] >> CASE_TAC >> simp[]) >>
  `R (jump_to exit u)` by metis_tac[] >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def, Abbr `u`,
      update_var_def, FLOOKUP_UPDATE]
QED

Theorem rest_word_incr_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := label;
      bb_instructions := [mk_inst a ADD [Var idx; Lit 1w] [next];
                          mk_inst b ASSIGN [Var next] [idx];
                          mk_inst c JMP [Label cond_lbl] []]|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  rest_word_membership_inv idx result len needle elem R i s /\
  i < len /\ elem i <> needle /\ idx <> result /\ next <> result /\
  R (update_var idx (n2w (i+1)) (update_var next (n2w (i+1)) s)) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      rest_word_membership_inv idx result len needle elem R (i+1) t
Proof
  strip_tac >>
  `eval_operand (Var idx) s = SOME (n2w i)` by
    gvs[rest_word_membership_inv_def] >>
  `(n2w i:bytes32) + 1w = n2w (i+1)` by
    (irule (cj 1 rest_word_membership_next_word) >>
     gvs[rest_word_membership_inv_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `R u` >>
  `run_inst_seq [mk_inst a ADD [Var idx; Lit 1w] [next];
                 mk_inst b ASSIGN [Var next] [idx]] s = OK u` by
    (gvs[eval_operand_def, lookup_var_def] >>
     simp_tac (srw_ss()) [Once exprLoweringPropsTheory.run_inst_seq_def] >>
     once_rewrite_tac [step_inst_base_def] >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     simp[exec_pure2_def, eval_operand_def, lookup_var_def] >>
     simp_tac (srw_ss()) [Once exprLoweringPropsTheory.run_inst_seq_def] >>
     once_rewrite_tac [step_inst_base_def] >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     simp[exprLoweringPropsTheory.run_inst_seq_def, Abbr `u`, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexists `jump_to cond_lbl u` >> conj_tac
  >- (irule rest_word_block_path >> simp[Once CONJ_ASSOC] >>
      qexists `cond_lbl` >>
      simp[Abbr `u`, update_var_def, jump_to_def, mk_inst_def,
           step_inst_base_def, is_terminator_def,
           fragExecMemTheory.run_inst_seq_mem_ok_def] >>
      strip_tac >> gvs[eval_operand_def, lookup_var_def] >>
      simp[exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
           FLOOKUP_UPDATE] >>
      conj_tac >> irule below_frontier_no_ranges >> simp[]) >>
  `R (jump_to cond_lbl u)` by metis_tac[] >>
  gvs[rest_word_membership_inv_def, jump_to_def, eval_operand_def,
      lookup_var_def, Abbr `u`, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[] >>
  first_x_assum irule >> decide_tac
QED

Theorem rest_word_layout_exit_path:
  rest_word_loop_layout cs ct fn needle arr len stride off is_in out h code /\
  s.vs_current_bb = h.rw_exit /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand (Var h.rw_result) s = SOME (bool_to_word found) /\ R s /\
  (!v. ~is_in /\ out = Var v ==>
       R (update_var v (bool_to_word (~found)) s)) /\
  (!u k. R u ==> R (u with vs_inst_idx := k)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = ct.cs_current_bb /\
      t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
      eval_operand out t = SOME (bool_to_word (if is_in then found else ~found)) /\ R t
Proof
  strip_tac >> drule rest_word_loop_layout_exit >> strip_tac >>
  Cases_on `is_in` >> gvs[]
  >- (qexists `s` >> simp[] >>
      mp_tac (Q.INST [`code` |-> `[]`, `t` |-> `s`] rest_word_sequence_marked) >>
      simp[exprLoweringPropsTheory.run_inst_seq_def,
           fragExecMemTheory.run_inst_seq_mem_ok_def]) >>
  qabbrev_tac `insts = [mk_inst a ISZERO [Var h.rw_result] [v]]` >>
  qexists `(update_var v (bool_to_word (~found)) s) with vs_inst_idx := 1` >>
  conj_tac
  >- (mp_tac (Q.INST [`code` |-> `insts`,
         `t` |-> `update_var v (bool_to_word (~found)) s`] rest_word_sequence_marked) >>
      simp[Abbr `insts`, mk_inst_def, is_terminator_def,
           exprLoweringPropsTheory.run_inst_seq_def,
           fragExecMemTheory.run_inst_seq_mem_ok_def] >>
      impl_tac
      >- (conj_tac >- gvs[mk_inst_def] >>
          Cases_on `found` >> gvs[bool_to_word_def] >>
          simp[step_inst_base_ISZERO, exec_pure1_def, bool_to_word_def] >>
          strip_tac >> irule below_frontier_no_ranges >> simp[]) >> simp[]) >>
  simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem rest_word_body_address_sequence:
  !idx s i arr baseword mul total stride off a b c addr.
  eval_operand (Var idx) s = SOME (n2w i) /\
  eval_operand arr s = SOME baseword /\
  arr <> Var mul /\ arr <> Var total ==>
  let p = update_var mul (n2w (i * stride)) s in
  let q = if 0 < off then update_var total (n2w (off + i * stride)) p else p in
  run_inst_seq
    ([mk_inst a MUL [Var idx; Lit (n2w stride)] [mul]] ++
     (if 0 < off then [mk_inst b ADD [Lit (n2w off); Var mul] [total]] else []) ++
     [mk_inst c ADD [arr; if 0 < off then Var total else Var mul] [addr]]) s =
    OK (update_var addr (baseword + n2w (off + i * stride)) q)
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `arr` >> gvs[eval_operand_def] >>
  Cases_on `0 < off` >>
  gvs[exprLoweringPropsTheory.run_inst_seq_def, mk_inst_def,
      step_inst_base_opcode_eqs, exec_pure2_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      word_mul_n2w, word_add_n2w]
QED

Theorem rest_word_body_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := label; bb_instructions := pre ++ loads ++
      [mk_inst a EQ [valueop; needleop] [matched];
       mk_inst b JNZ [Var matched; Label found; Label incr] []]|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  rest_word_membership_inv idx result len needle elem R i s /\
  run_inst_seq pre s = OK p /\ run_inst_seq loads p = OK q /\
  EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\
              j.inst_opcode <> GAS) (pre ++ loads) /\
  (memory ==> run_inst_seq_mem_ok pre s /\ run_inst_seq_mem_ok loads p) /\
  q.vs_current_bb = s.vs_current_bb /\ ~q.vs_halted /\
  FLOOKUP q.vs_vars idx = FLOOKUP s.vs_vars idx /\
  FLOOKUP q.vs_vars result = FLOOKUP s.vs_vars result /\
  eval_operand valueop q = SOME (elem i) /\
  eval_operand needleop q = SOME needle /\
  matched <> idx /\ matched <> result /\
  R (update_var matched (bool_to_word (elem i = needle)) q) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = (if elem i = needle then found else incr) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      rest_word_membership_inv idx result len needle elem R i t
Proof
  strip_tac >>
  `step_inst_base (mk_inst a EQ [valueop; needleop] [matched]) q =
     OK (update_var matched (bool_to_word (elem i = needle)) q)` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def]) >>
  qmatch_asmsub_abbrev_tac `R u` >>
  `run_inst_seq (pre ++ loads ++ [mk_inst a EQ [valueop; needleop] [matched]]) s = OK u` by
    (rewrite_tac[GSYM APPEND_ASSOC] >>
     qpat_assum `run_inst_seq pre s = OK p`
       (fn th => rewrite_tac[MATCH_MP exprLoweringPropsTheory.run_inst_seq_append th]) >>
     qpat_assum `run_inst_seq loads p = OK q`
       (fn th => rewrite_tac[MATCH_MP exprLoweringPropsTheory.run_inst_seq_append th]) >>
     simp[exprLoweringPropsTheory.run_inst_seq_def]) >>
  `memory ==> run_inst_seq_mem_ok
      (pre ++ loads ++ [mk_inst a EQ [valueop; needleop] [matched]]) s` by
    (strip_tac >> rewrite_tac[GSYM APPEND_ASSOC] >>
     irule fragExecMemTheory.run_inst_seq_mem_ok_append >> simp[] >>
     irule fragExecMemTheory.run_inst_seq_mem_ok_append >> simp[] >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  qexists `jump_to (if elem i = needle then found else incr) u` >> conj_tac
  >- (irule rest_word_block_path >> simp[Once CONJ_ASSOC] >>
      qexists `if elem i = needle then found else incr` >>
      simp[EVERY_APPEND, Abbr `u`, update_var_def, mk_inst_def, is_terminator_def] >>
      reverse conj_tac >- simp[jump_to_def] >>
      Cases_on `elem i = needle` >>
      simp[step_inst_base_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE, bool_to_word_def]) >>
  `R (jump_to (if elem i = needle then found else incr) u)` by metis_tac[] >>
  `rest_word_membership_inv idx result len needle elem R i u` by
    (irule rest_word_membership_inv_frame >> simp[] >> qexists `s` >>
     simp[Abbr `u`, update_var_def, FLOOKUP_UPDATE]) >>
  gvs[rest_word_membership_inv_def, jump_to_def, eval_operand_def,
      lookup_var_def, Abbr `u`, update_var_def]
QED

Theorem rest_word_body_loaded_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := label; bb_instructions :=
      [mk_inst a MUL [Var idx; Lit (n2w stride)] [mulvar]] ++
      (if 0 < off then [mk_inst b ADD [Lit (n2w off); Var mulvar] [totalvar]] else []) ++
      [mk_inst c ADD [arr; if 0 < off then Var totalvar else Var mulvar] [addrvar]] ++
      loads ++ [mk_inst d EQ [valueop; needleop] [matched];
                mk_inst e JNZ [Var matched; Label found; Label incr] []]|> /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  rest_word_membership_inv idx result len needle elem R i s /\
  eval_operand arr s = SOME baseword /\
  arr <> Var mulvar /\ arr <> Var totalvar /\
  ~MEM idx [mulvar; totalvar; addrvar] /\
  ~MEM result [mulvar; totalvar; addrvar] /\
  p = update_var addrvar (baseword + n2w (off + i * stride))
        (if 0 < off then update_var totalvar (n2w (off + i * stride))
            (update_var mulvar (n2w (i * stride)) s)
         else update_var mulvar (n2w (i * stride)) s) /\
  run_inst_seq loads p = OK q /\
  EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\
              j.inst_opcode <> GAS) loads /\
  (memory ==> run_inst_seq_mem_ok loads p) /\
  q.vs_current_bb = p.vs_current_bb /\ ~q.vs_halted /\
  FLOOKUP q.vs_vars idx = FLOOKUP p.vs_vars idx /\
  FLOOKUP q.vs_vars result = FLOOKUP p.vs_vars result /\
  eval_operand valueop q = SOME (elem i) /\ eval_operand needleop q = SOME needle /\
  matched <> idx /\ matched <> result /\
  R (update_var matched (bool_to_word (elem i = needle)) q) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = (if elem i = needle then found else incr) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      rest_word_membership_inv idx result len needle elem R i t
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `<|bb_label := label; bb_instructions := pre ++ loads ++ suffix|>` >>
  `run_inst_seq pre s = OK p` by
    (qpat_assum `p = _` SUBST1_TAC >> simp[Abbr `pre`] >>
     irule (SRULE [LET_THM] rest_word_body_address_sequence) >>
     simp[] >> gvs[rest_word_membership_inv_def]) >>
  `run_inst_seq_mem_ok pre s` by
    (irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
     Cases_on `0 < off` >> simp[Abbr `pre`, mk_inst_def] >>
     rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]) >>
  `p.vs_current_bb = s.vs_current_bb /\
   FLOOKUP p.vs_vars idx = FLOOKUP s.vs_vars idx /\
   FLOOKUP p.vs_vars result = FLOOKUP s.vs_vars result` by
    (qpat_assum `p = _` SUBST1_TAC >> Cases_on `0 < off` >>
     gvs[update_var_def, FLOOKUP_UPDATE]) >>
  irule rest_word_body_path >>
  simp[Once CONJ_ASSOC, Abbr `suffix`, mk_inst_def] >>
  qexistsl [`loads`, `p`, `pre`, `q`] >>
  Cases_on `0 < off` >>
  simp[EVERY_APPEND, Abbr `pre`, mk_inst_def, is_terminator_def]
QED
