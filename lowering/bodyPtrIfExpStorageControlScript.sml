Theory bodyPtrIfExpStorageControl
Ancestors
  bodyPtrIfExpStorageBodyPost copyExecution slotCopyExecution
  fragGasPathPtr fragGasSeqPtr gasCount ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomState venomInst emitHelper
  contextCodegenRel codegenRel exprLoweringProps compileEnv finite_map words

Theorem ifexp_copy_body_fetch:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = slot_copy_body cs /\ s.vs_inst_idx = 0 ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (TAKE 7 (slot_copy_body_insts cs src dst load))
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    get_instruction bb (s.vs_inst_idx+7) =
      SOME (mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] [])
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  qexists_tac `<|bb_label := slot_copy_body cs;
    bb_instructions := slot_copy_body_insts cs src dst load|>` >>
  simp[get_instruction_def, slot_copy_body_insts_def]
QED

Theorem ifexp_copy_eq_ghost[local]:
  op_taint tn (Var (slot_copy_var cs 0)) = {} ==>
  step_prov PG G
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
      [slot_copy_var cs 1]) (update_var (slot_copy_var cs 1) w s) =
    DRESTRICT G (COMPL {slot_copy_var cs 1}) /\
  step_taint
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
      [slot_copy_var cs 1]) s (update_var (slot_copy_var cs 1) w s) tn =
    tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{})
Proof
  strip_tac >>
  `new_site_bytes s (update_var (slot_copy_var cs 1) w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  Cases_on `eval_operand (Var (slot_copy_var cs 0)) s` >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
    adopt_reset_def, set_var_taint_def, out_taint_def, op_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, update_var_def, taint_component_equality]
QED

Theorem ifexp_copy_eq_check[local]:
  ~ctx_has_dalloca ctx /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE ==>
  ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
      [slot_copy_var cs 1]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_prov_def, op_taint_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  conj_tac >-
    (gen_tac >> Cases_on `op = Var (slot_copy_var cs 0)` >>
     gvs[op_taint_def] >> Cases_on `op = Lit (n2w n)` >> gvs[]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                  combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem ifexp_copy_eq_run[local]:
  i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) ==>
  step_inst_base
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
      [slot_copy_var cs 1]) s =
  OK (update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)
Proof
  strip_tac >>
  `((n2w i : bytes32) = n2w n) <=> (i=n)` by
    (pure_rewrite_tac[n2w_11] >> fs[dimword_def]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                  combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def]
QED

Theorem ifexp_copy_condition_eq_path:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {slot_copy_var cs 1}))
    (tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{}))
    (OK ((update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)
      with vs_inst_idx := 1))
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  `step_inst_base
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
      [slot_copy_var cs 1]) s =
    OK (update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)` by
    (irule ifexp_copy_eq_run >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {slot_copy_var cs 1}))
    (tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{}))
    (OK ((update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)
      with vs_inst_idx := 1))` by
    (`step_prov PG G
       (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
         [slot_copy_var cs 1]) (update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s) =
       DRESTRICT G (COMPL {slot_copy_var cs 1}) /\
      step_taint
       (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
         [slot_copy_var cs 1]) s (update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s) tn =
       tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{})` by
        (irule ifexp_copy_eq_ghost >> simp[]) >>
     qpat_x_assum `step_taint _ _ _ _ = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     qpat_x_assum `step_prov _ _ _ _ = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexistsl_tac [`0`,
       `mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0);Lit (n2w n)]
         [slot_copy_var cs 1]`] >>
     simp[gas_count_step_def, step_inst_non_invoke, get_instruction_def,
          slot_copy_cond_insts_def, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (simp[GSYM mk_inst_def, ptr_safe_step_def] >>
        irule ifexp_copy_eq_check >> simp[]) >>
     simp[NoAsms, GSYM mk_inst_def] >> disj1_tac >>
     conj_tac >- simp[update_var_def] >>
     sym_tac >> irule ghost_step_non_invoke >>
     simp[mk_inst_def, step_inst_non_invoke] >> gvs[mk_inst_def]) >>
  `~((update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)
       with vs_inst_idx := 1).vs_halted` by simp[update_var_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_condition_jnz_path:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 1 /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var (slot_copy_var cs 1) s = SOME (bool_to_word test) /\
  op_taint tn (Var (slot_copy_var cs 1)) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if test then slot_copy_exit cs else slot_copy_body cs) s))
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  `step_inst_base (mk_inst (cs.cs_next_id+3) JNZ
    [Var (slot_copy_var cs 1);Label (slot_copy_exit cs);Label (slot_copy_body cs)] []) s =
    OK (jump_to (if test then slot_copy_exit cs else slot_copy_body cs) s)` by
    (`eval_operand (Var (slot_copy_var cs 1)) s = SOME (bool_to_word test)` by
       simp[eval_operand_def] >>
     drule venomExecProofsTheory.step_jnz_behavior >>
     disch_then (qspecl_then [`slot_copy_exit cs`, `slot_copy_body cs`,
       `cs.cs_next_id+3`] mp_tac) >>
     Cases_on `test` >> gvs[mk_inst_def, venomExecSemanticsTheory.bool_to_word_def]) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn (mk_inst (cs.cs_next_id+3) JNZ
    [Var (slot_copy_var cs 1);Label (slot_copy_exit cs);Label (slot_copy_body cs)] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jnz_behavior, jump_to_def] >>
     Cases_on `test` >> gvs[op_taint_def, bool_to_word_def] >>
     gen_tac >> Cases_on `op = Var (slot_copy_var cs 1)` >> gvs[] >>
     Cases_on `op = Label (slot_copy_exit cs)` >> gvs[] >>
     Cases_on `op = Label (slot_copy_body cs)` >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if test then slot_copy_exit cs else slot_copy_body cs) s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[get_instruction_def, slot_copy_cond_insts_def, step_inst_non_invoke,
          mk_inst_def, gas_count_step_def, step_jnz_behavior, is_terminator_def] >>
     Cases_on `test` >> gvs[mk_inst_def, bool_to_word_def] >> metis_tac[]) >>
  `~(jump_to (if test then slot_copy_exit cs else slot_copy_body cs) s).vs_halted` by
    simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_condition_path:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {slot_copy_var cs 1}))
    (tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{}))
    (OK (slot_copy_cond_result cs n i s))
Proof
  strip_tac >>
  qabbrev_tac `u = (update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)
    with vs_inst_idx := 1` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {slot_copy_var cs 1})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u)` by
    (simp[Abbr `u`, Abbr `G1`, Abbr `tn1`] >>
     irule ifexp_copy_condition_eq_path >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 u 0 G1 tn1
    (OK (jump_to (if i=n then slot_copy_exit cs else slot_copy_body cs) u))` by
    (irule ifexp_copy_condition_jnz_path >>
     simp[Abbr `u`, Abbr `tn1`, update_var_def, lookup_var_def,
          op_taint_def, FLOOKUP_UPDATE] >>
     qexistsl_tac [`dst`, `load`, `n`, `src`] >> simp[]) >>
  `jump_to (if i=n then slot_copy_exit cs else slot_copy_body cs) u =
    slot_copy_cond_result cs n i s` by
    simp[Abbr `u`, slot_copy_cond_result_def, jump_to_def] >>
  fs[Abbr `G1`, Abbr `tn1`] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_condition_transition:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK (slot_copy_cond_result cs n i s)) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> slot_copy_var cs 1 ==>
      lookup_var x (slot_copy_cond_result cs n i s) = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qexistsl_tac [`DRESTRICT G (COMPL {slot_copy_var cs 1})`,
    `tn with t_var := tn.t_var |+ (slot_copy_var cs 1,{})`] >>
  conj_tac >- (irule ifexp_copy_condition_path >> metis_tac[]) >>
  gvs[op_prov_def, op_taint_def] >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, slot_copy_var_distinct,
       slot_copy_cond_result_def, lookup_var_def, update_var_def, jump_to_def]
QED
