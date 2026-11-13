(* Counted execution of fixed-array normalization control windows. *)
Theory typedNormalizeFixedLoopPathMem
Ancestors
  typedNormalizeLoop typedNormalizeStraightPathMem typedArrayLoopLayoutMem
  typedArrayLoopControlMem fragGasSeqMem fragGasMode fragGasPathMem fragExecMem
  memSafeRun instMemFrontier venomExecProofs arithmetic emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState list rich_list words

Theorem typed_sa_pointer_mem_path:
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [dso];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var dso] [dp]] /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code bb.bb_instructions /\
  ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]) /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 ==>
  ?u. gas_marked_path T ctx fn s 0 (OK u) /\
    u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (a+ss*i)) /\
    eval_operand (Var dp) u = SOME (n2w (b+ds*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sa_pointer_run >>
  disch_then (qspecl_then [`ss`, `id`, `ds`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := 4))` by
    (`EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) code /\
      LENGTH (FILTER (\j. j.inst_opcode = GAS) code) = 0 /\
      LENGTH code = 4` by simp[mk_inst_def, is_terminator_def] >>
     `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
       gvs[] >>
     `run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK q` by
       asm_rewrite_tac[] >>
     drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  qexists_tac `q with vs_inst_idx := 4` >>
  fs[gas_marked_path_def, venom_state_component_equality,
     eval_operand_def, lookup_var_def]
QED

Theorem typed_sa_header_mem_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done n body_lbl exit|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= n /\ n < dimword(:256) ==>
  gas_marked_path T ctx fn s 0
    (OK (jump_to (if i < n then body_lbl else exit)
      (typed_sa_header_state cmp done i n s)))
Proof
  strip_tac >>
  `run_inst_seq (TAKE 2 (typed_sa_header_insts id ctr cmp done n body_lbl exit)) s =
    OK (typed_sa_header_state cmp done i n s)` by
    (irule typed_sa_header_prefix >> simp[] >> goal_assum (drule_at Any)) >>
  `run_inst_seq_mem_ok
    (TAKE 2 (typed_sa_header_insts id ctr cmp done n body_lbl exit)) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[typed_sa_header_insts_def, mk_inst_def, below_frontier_no_ranges]) >>
  `gas_path_mem ctx fn s 0
    (OK (typed_sa_header_state cmp done i n s with vs_inst_idx := 2))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >>
     simp[typed_sa_header_insts_def, mk_inst_def, is_terminator_def] >>
     disch_then irule >> simp[] >> goal_assum (drule_at Any)) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s 0 (OK u)` >>
  `gas_path_mem_edge ctx fn u 0
    (OK (jump_to (if i < n then body_lbl else exit)
      (typed_sa_header_state cmp done i n s)))` by
    (simp[gas_path_mem_edge_def] >>
     conj_tac >- simp[Abbr `u`, typed_sa_header_state_def, update_var_def] >>
     qexists_tac `0` >>
     simp[Abbr `u`, typed_sa_header_insts_def, typed_sa_header_state_def,
       update_var_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       mem_safe_step_non_invoke, below_frontier_no_ranges,
       gasCountTheory.gas_count_step_def, is_terminator_def,
       bool_to_word_def, jump_to_def] >>
     Cases_on `i < n` >> simp[] >> metis_tac[]) >>
  simp[gas_marked_path_def] >>
  `gas_path_mem ctx fn u 0
    (OK (jump_to (if i < n then body_lbl else exit)
      (typed_sa_header_state cmp done i n s)))` by
    (drule (cj 2 gas_path_mem_rules) >>
     disch_then (qspec_then `0` mp_tac) >>
     simp[jump_to_def, typed_sa_header_state_def, update_var_def,
          cj 1 gas_path_mem_rules]) >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem typed_sa_jump_mem_path[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) /\
  ~s.vs_halted ==>
  gas_path_mem ctx fn s 0 (OK (jump_to hdr s))
Proof
  strip_tac >>
  `gas_path_mem_edge ctx fn s 0 (OK (jump_to hdr s))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges,
       gasCountTheory.gas_count_step_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `hdr` >> simp[]) >>
  drule (cj 2 gas_path_mem_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[jump_to_def, cj 1 gas_path_mem_rules]
QED

Theorem typed_sa_initial_mem_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  gas_marked_path T ctx fn s 0 (OK (jump_to hdr (update_var ctr 0w s)))
Proof
  strip_tac >>
  `run_inst_seq [mk_inst id ASSIGN [Lit 0w] [ctr]] s =
    OK (update_var ctr 0w s)` by
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure1_def, eval_operand_def] >>
  `run_inst_seq_mem_ok [mk_inst id ASSIGN [Lit 0w] [ctr]] s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, below_frontier_no_ranges]) >>
  `gas_path_mem ctx fn s 0
    (OK (update_var ctr 0w s with vs_inst_idx := s.vs_inst_idx + 1))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> simp[DROP_APPEND, update_var_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s 0 (OK u)` >>
  `gas_path_mem ctx fn u 0 (OK (jump_to hdr (update_var ctr 0w s)))` by
    (`jump_to hdr (update_var ctr 0w s) = jump_to hdr u` by
       simp[Abbr `u`, jump_to_def] >>
     asm_rewrite_tac[] >> irule typed_sa_jump_mem_path >>
     conj_tac >- simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`bb`, `id+1`] >>
     simp[Abbr `u`, update_var_def, get_instruction_def, EL_APPEND2]) >>
  simp[gas_marked_path_def] >> drule_all gas_path_mem_then >> simp[]
QED

Theorem typed_sa_backedge_mem_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) ==>
  gas_marked_path T ctx fn s 0
    (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s)))
Proof
  strip_tac >>
  `run_inst_seq (TAKE 2 (typed_sa_backedge_insts id ctr nv hdr)) s =
    OK (typed_sa_backedge_state ctr nv i s)` by
    simp[typed_sa_backedge_insts_def, typed_sa_backedge_state_def,
      run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, exec_pure1_def, eval_operand_def,
      lookup_var_update_var, GSYM word_add_n2w, ADD1] >>
  `run_inst_seq_mem_ok (TAKE 2 (typed_sa_backedge_insts id ctr nv hdr)) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[typed_sa_backedge_insts_def, mk_inst_def, below_frontier_no_ranges]) >>
  `gas_path_mem ctx fn s 0 (OK (typed_sa_backedge_state ctr nv i s
    with vs_inst_idx := s.vs_inst_idx + 2))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >>
     simp[typed_sa_backedge_insts_def, mk_inst_def, is_terminator_def] >>
     disch_then irule >> simp[DROP_APPEND] >> goal_assum (drule_at Any) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s 0 (OK u)` >>
  `gas_path_mem ctx fn u 0
    (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s)))` by
    (`jump_to hdr (typed_sa_backedge_state ctr nv i s) = jump_to hdr u` by
       simp[Abbr `u`, jump_to_def] >>
     asm_rewrite_tac[] >> irule typed_sa_jump_mem_path >>
     conj_tac >- simp[Abbr `u`, typed_sa_backedge_state_def, update_var_def] >>
     qexistsl_tac [`bb`, `id+2`] >>
     simp[Abbr `u`, typed_sa_backedge_state_def, update_var_def,
       get_instruction_def, typed_sa_backedge_insts_def, EL_APPEND2]) >>
  simp[gas_marked_path_def] >> drule_all gas_path_mem_then >> simp[]
QED
