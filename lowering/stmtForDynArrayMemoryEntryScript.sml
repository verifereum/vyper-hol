Theory stmtForDynArrayMemoryEntry
Ancestors
  whitelistForIterDynFrag stmtSimForArrayLoop stmtSimDeclPath stmtSimProps
  exprLoweringProps fragGasSeqMem fragGasPathMem fragExecMem allocaHistory
  allocaHistoryFragment entrySinkExtraction venomInstProofs venomExecSemantics venomState
  compileEnv loweringStateRelDefs loweringPosts words arithmetic list rich_list
  emitHelperProps loweringSlice finite_map
  venomInst venomExecProps memSafeRun instMemFrontier gasCount unitTransformDefs codegenRel contextCodegenRel

Theorem dynarray_entry_seq_mem[local]:
  ~s.vs_halted /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = code ++ [mk_inst j JMP [Label target] []] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t ==>
  gas_path_mem ctx func s 0 (OK (jump_to target t)) /\
  alloca_history func (jump_to target t)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK mid)` >>
  `mid.vs_current_bb = s.vs_current_bb /\ ~mid.vs_halted` by
    (simp[Abbr `mid`] >> metis_tac[run_inst_seq_preserves_entry_control]) >>
  `get_instruction bb mid.vs_inst_idx = SOME (mk_inst j JMP [Label target] [])` by
    (`s.vs_inst_idx + LENGTH code < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP] >> decide_tac) >>
     simp[Abbr `mid`, get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `\l. EL (LENGTH code) l`) >>
     simp[EL_DROP, EL_APPEND_EQN, ADD_COMM]) >>
  `gas_path_mem_edge ctx func mid 0 (OK (jump_to target mid))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[gas_count_step_def, mem_safe_step_non_invoke, step_inst_non_invoke,
          step_inst_base_opcode_eqs, is_terminator_def, inst_dload_in_section_def] >>
     conj_tac >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `target` >> simp[]) >>
  `jump_to target mid = jump_to target t` by (simp[Abbr `mid`, jump_to_def] >> gvs[]) >>
  `gas_path_mem ctx func mid 0 (OK (jump_to target t))` by
    (`~(jump_to target mid).vs_halted` by (simp[NoAsms, jump_to_def] >> first_assum ACCEPT_TAC) >>
     `gas_path_mem ctx func (jump_to target mid) 0 (OK (jump_to target mid))` by
       (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
     drule_all (cj 2 gas_path_mem_rules) >> simp[]) >>
  qpat_x_assum `!ctx. gas_path_mem _ _ _ _ _` (qspec_then `ctx` assume_tac) >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  irule alloca_history_jump >> simp[jump_to_def] >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + LENGTH code` >> simp[]
QED

Theorem dynarray_loop_initialize_mem:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\
  ret_pc_ok cenv st s0 /\
  ALL_DISTINCT [lv; p; idx; g; vld] /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv; p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv; p; idx; g; vld]) /\
  alloca_history func s0 /\ w2n array_base + 32 <= s0.vs_alloca_next ==>
  ?dst cc s1.
    exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0) (n2w sz : bytes32) = OK s1 /\
    cc = jump_to cond (update_var vld 1w (update_var g 0w
      (update_var idx 0w (jump_to entry s1)))) /\
    array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    gas_path_mem ctx func s0 0 (OK cc) /\
    alloca_history func cc /\ cc.vs_memory = s0.vs_memory /\
    s0.vs_alloca_next <= cc.vs_alloca_next
Proof
  strip_tac >> drule_all dynarray_loop_initialize_explicit >> strip_tac >>
  `gas_path_mem ctx func s0 0 (OK cc) /\ alloca_history func cc` by
    suspend "certificate" >>
  qexistsl_tac [`dst`, `cc`, `s1`] >> simp[] >>
  drule exec_alloca_memory >> simp[update_var_def, jump_to_def] >> strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, AllCaseEqs()]
QED
Resume dynarray_loop_initialize_mem[certificate]:
  qabbrev_tac `sl = update_var lv (n2w (LENGTH vs)) s0` >>
  `step_inst_base (mk_inst mi MLOAD [saved_base] [lv]) s0 = OK sl` by
    (simp[Abbr `sl`] >> qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
     irule step_MLOAD >> simp[]) >>
  `step_inst_base ainst sl = OK s1` by
    simp[step_inst_base_opcode_eqs, eval_operand_def] >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `run_inst_seq_mem_ok [mk_inst mi MLOAD [saved_base] [lv]; ainst] s0` by
    (simp[run_inst_seq_mem_ok_def, below_frontier_MLOAD, inst_dload_in_section_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `run_inst_seq [mk_inst mi MLOAD [saved_base] [lv]; ainst] s0 = OK s1` by
    simp[run_inst_seq_def] >>
  `gas_path_mem ctx func s0 0 (OK (jump_to entry s1)) /\
   alloca_history func (jump_to entry s1)` by
    (irule dynarray_entry_seq_mem >>
     simp[] >>
     qexistsl_tac [`[mk_inst mi MLOAD [saved_base] [lv]; ainst]`, `j`] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `en = jump_to entry s1` >>
  `stmt_state_rel ctx func cenv cx es sl` by
    (simp[Abbr `sl`] >> irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (drule_all stmt_state_rel_exec_alloca >> simp[] >>
     disch_then irule >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es en` by simp[Abbr `en`, stmt_state_rel_jump_to] >>
  `alloca_inv en` by fs[stmt_state_rel_def] >>
  `~en.vs_halted` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[Abbr `en`, Abbr `sl`, update_var_def, jump_to_def, AllCaseEqs()]) >>
  `lookup_var lv en = SOME (n2w (LENGTH vs))` by
    (drule_all exec_alloca_frames >> strip_tac >>
     fs[ALL_DISTINCT, Abbr `en`, jump_to_def, lookup_var_def,
        Abbr `sl`, update_var_def, FLOOKUP_UPDATE]) >>
  suspend "entry_certificate"
QED
Resume dynarray_loop_initialize_mem[entry_certificate]:
  `run_inst_seq
     [mk_inst e1 ASSIGN [Lit 0w] [idx];
      mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
      mk_inst e3 ISZERO [Var g] [vld];
      mk_inst e4 ASSERT [Var vld] []] en =
    OK (update_var vld 1w (update_var g 0w (update_var idx 0w en)))` by
    (irule dynarray_entry_block_run >> fs[ALL_DISTINCT] >>
     qexists_tac `LENGTH vs` >> simp[]) >>
  `run_inst_seq_mem_ok
     [mk_inst e1 ASSIGN [Lit 0w] [idx];
      mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
      mk_inst e3 ISZERO [Var g] [vld];
      mk_inst e4 ASSERT [Var vld] []] en` by
    (fs[ALL_DISTINCT] >>
     simp[run_inst_seq_mem_ok_def, inst_dload_in_section_def,
          step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
          exec_pure2_def, exec_pure1_def, lookup_var_update_var,
          bool_to_word_def, inst_mem_below_frontier_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `gas_path_mem ctx func en 0 (OK cc) /\ alloca_history func cc` by
    (qpat_x_assum `cc = _` SUBST1_TAC >>
     irule dynarray_entry_seq_mem >> simp[Abbr `en`, jump_to_def] >>
     qexists_tac `e5` >>
     fs[mk_inst_def, is_terminator_def, jump_to_def]) >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >> simp[]
QED
Finalise dynarray_loop_initialize_mem
