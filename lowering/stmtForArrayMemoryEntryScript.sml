Theory stmtForArrayMemoryEntry
Ancestors
  stmtForArrayControlMemory stmtSimForArrayFrag stmtSimDeclPath loweringSlice
  stmtSimForArrayLoop compileEnv loweringStateRelDefs loweringPosts venomExecSemantics venomState
  allocaHistory fragGasSeqMem fragGasPathMem memSafeRun instMemFrontier
  venomInst gasCount words arithmetic list finite_map
  stmtSimProps exprLoweringProps venomExecProps

Theorem array_loop_initialize_mem:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\ name <> id /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar saved_base arr_sz) /\
  eval_operand saved_base s0 = SOME array_base /\ ret_pc_ok cenv st s0 /\
  (!x. not_fresh_at caller x ==> x <> p /\ x <> idx) /\
  alloca_history func s0 ==>
  ?s1 dst s.
    exec_alloca ainst s0 (n2w sz : bytes32) = OK s1 /\
    s = jump_to cond (update_var idx 0w (jump_to entry s1)) /\
    array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es s /\ gas_path_mem ctx func s0 0 (OK s) /\
    (!x. not_fresh_at caller x ==> lookup_var x s = lookup_var x s0) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s0.vs_memory /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    alloca_history func s
Proof
  strip_tac >>
  `ainst.inst_outputs = [p] /\ ainst.inst_opcode = ALLOCA /\
   MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved bc sa /\
   FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
   (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
   bc.ce_imm_alloca = cenv.ce_imm_alloca /\
   not_local_ptr cenv es.scopes idx /\ p <> idx /\
   (!x. saved_base = Var x ==> x <> idx)` by
    (fs[array_for_code_def] >>
     qpat_x_assum `_ = cenv` (mp_tac o Q.AP_TERM `\e. e.ce_imm_alloca`) >>
     simp[] >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes p /\ saved_base <> Var p` by
    suspend "allocation_safe" >>
  `?s1. exec_alloca ainst s0 (n2w sz : bytes32) = OK s1` by
    (simp[exec_alloca_def] >>
     Cases_on `FLOOKUP s0.vs_allocas ainst.inst_id` >> simp[] >>
     PairCases_on `x` >> simp[]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  rename1 `lookup_var p s1 = SOME dst` >>
  qexistsl_tac [`s1`, `dst`, `jump_to cond (update_var idx 0w (jump_to entry s1))`] >>
  simp[] >> suspend "finish"
QED
Resume array_loop_initialize_mem[allocation_safe]:
  fs[not_local_ptr_def, local_ptrs_reserved_def] >>
  `!nm z. FLOOKUP bc.ce_vars nm = SOME (PtrVar (Var p) z) ==> nm = id` by
    metis_tac[] >>
  conj_tac
  >- (conj_tac
      >- (rpt strip_tac >> Cases_on `name' = id` >> gvs[] >> metis_tac[]) >>
      metis_tac[]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED
Resume array_loop_initialize_mem[finish]:
  drule_all exec_alloca_frames >> strip_tac >>
  drule exec_alloca_memory >> strip_tac >>
  `s1.vs_current_bb = s0.vs_current_bb /\ s1.vs_inst_idx = s0.vs_inst_idx /\
   ~s1.vs_halted /\ s0.vs_alloca_next <= s1.vs_alloca_next` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def, AllCaseEqs()]) >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "path" >>
  conj_tac
  >- (rpt strip_tac >> simp[jump_to_def, update_var_def, lookup_var_def,
                           FLOOKUP_UPDATE] >>
      `x <> p /\ x <> idx` by metis_tac[] >>
      gvs[lookup_var_def] >> metis_tac[]) >>
  simp[jump_to_def, update_var_def] >>
  suspend "history"
QED
Resume array_loop_initialize_mem[invariant]:
  `stmt_state_rel ctx func cenv cx es (update_var idx 0w (jump_to entry s1))` by
    (irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to]) >>
  `eval_operand saved_base s1 = SOME array_base` by
    (drule_all exec_alloca_operand_frame >> simp[]) >>
  `eval_operand saved_base (update_var idx 0w (jump_to entry s1)) = SOME array_base` by
    (irule eval_operand_update_other_local >> conj_tac
     >- metis_tac[] >>
     Cases_on `saved_base` >> gvs[eval_operand_def, jump_to_def, lookup_var_def]) >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[ret_pc_ok_def, lookup_var_def] >>
  rpt strip_tac >>
  qpat_x_assum `!x sz'. _` drule >> strip_tac >>
  simp[FLOOKUP_UPDATE] >> Cases_on `idx = x` >> simp[] >>
  Cases_on `p = x` >> gvs[] >> metis_tac[]
QED
Resume array_loop_initialize_mem[path]:
  `step_inst_base ainst s0 = OK s1` by
    simp[step_inst_base_opcode_eqs, eval_operand_def] >>
  `gas_path_mem_edge ctx func s0 0
     (OK (s1 with vs_inst_idx := SUC (LENGTH pre)))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[is_terminator_def, inst_dload_in_section_def] >>
     disch_then irule >> conj_tac
     >- (goal_assum (drule_at Any) >>
         simp[get_instruction_def, EL_APPEND_EQN]) >>
     irule below_frontier_no_ranges >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func s0 0 (OK a)` >>
  `gas_path_mem_edge ctx func a 0 (OK (jump_to entry a))` by
    (simp[gas_path_mem_edge_def, Abbr `a`] >> qexists_tac `0` >>
     qexists_tac `mk_inst j JMP [Label entry] []` >>
     simp[get_instruction_def, EL_APPEND_EQN, gas_count_step_def,
          mem_safe_step_non_invoke, step_inst_non_invoke,
          step_inst_base_opcode_eqs, is_terminator_def, inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `entry` >>
     simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  `jump_to entry a = jump_to entry s1` by simp[Abbr `a`, jump_to_def] >>
  `step_inst_base (mk_inst ei ASSIGN [Lit 0w] [idx]) (jump_to entry s1) =
     OK (update_var idx 0w (jump_to entry s1))` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  `gas_path_mem_edge ctx func (jump_to entry s1) 0
     (OK ((update_var idx 0w (jump_to entry s1)) with vs_inst_idx := 1))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[mk_inst_def, jump_to_def, get_instruction_def, is_terminator_def,
          inst_dload_in_section_def] >>
     disch_then irule >> conj_tac
     >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func (jump_to entry s1) 0 (OK b)` >>
  suspend "last_jump"
QED
Resume array_loop_initialize_mem[history]:
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `step_inst_base ainst s0 = OK s1` by
    simp[step_inst_base_opcode_eqs, eval_operand_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) alloca_history_base_step >>
  simp[is_terminator_def] >>
  disch_then (qspecl_then [`func`,
    `<|bb_label := lbl; bb_instructions := pre ++ [ainst; mk_inst j JMP [Label entry] []]|>`] mp_tac) >>
  impl_tac
  >- simp[get_instruction_def, EL_APPEND_EQN] >>
  strip_tac >> irule alloca_history_jump >>
  simp[] >> qexists_tac `s1 with vs_inst_idx := SUC (LENGTH pre)` >> simp[]
QED
Resume array_loop_initialize_mem[last_jump]:
  `b.vs_current_bb = entry /\ b.vs_inst_idx = 1 /\ ~b.vs_halted` by
    simp[Abbr `b`, update_var_def, jump_to_def] >>
  `step_inst_base (mk_inst ej JMP [Label cond] []) b = OK (jump_to cond b)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  `gas_path_mem_edge ctx func b 0 (OK (jump_to cond b))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst ej JMP [Label cond] []` >>
     simp[get_instruction_def, gas_count_step_def, mem_safe_step_non_invoke,
          step_inst_non_invoke, is_terminator_def, inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `cond` >> simp[]) >>
  `~(jump_to cond b).vs_halted` by simp[jump_to_def] >>
  `jump_to cond b = jump_to cond (update_var idx 0w (jump_to entry s1))` by
    simp[Abbr `b`, jump_to_def, update_var_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
Finalise array_loop_initialize_mem
