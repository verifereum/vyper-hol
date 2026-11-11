(* Memory-instrumented counted rounds for immutable array iteration. *)
Theory bodyImmRoundsMemory
Ancestors
  whitelistForIterImmLoop stmtForArrayMemoryRounds stmtForArrayControlMemory
  stmtForArrayMemoryRoundSupport stmtSimForArrayLoop stmtSimProps
  exprLoweringProps fragGasSeqMem fragGasPathMem fragGasMode fragExecMem
  allocaHistory venomInstProofs venomExecSemantics venomState compileEnv
  loweringPosts vyperState words arithmetic list finite_map venomInst
  venomExecProps memSafeRun instMemFrontier gasCount
Libs
  monadsyntax

Theorem immutable_condition_boundary_mem:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_arr_base arr_base p dst sz
    ainst cond caller k es s /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_arr_base = Var x ==> x <> dv) /\
  alloca_history func s ==>
  let t = jump_to (if k = LENGTH vs then exit else bod)
    (update_var dv (bool_to_word (k = LENGTH vs)) s) in
  array_loop_inv ctx func cenv cx P vs id idx saved_arr_base arr_base p dst sz
    ainst (if k = LENGTH vs then exit else bod) caller k es t /\
  gas_marked_path T ctx func s 0 (OK t) /\
  (!x. x <> dv ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_history func t
Proof
  strip_tac >> simp[] >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  irule alloca_history_jump >> simp[jump_to_def, update_var_def] >>
  qexists_tac `s` >> simp[]
QED

Resume immutable_condition_boundary_mem[invariant]:
  fs[array_loop_inv_def] >>
  `stmt_state_rel ctx func cenv cx es
    (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand saved_arr_base (update_var dv (bool_to_word (k = LENGTH vs)) s) = SOME arr_base` by
    (irule eval_operand_update_other_local >> simp[]) >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, ret_pc_ok_def] >>
  gvs[update_var_def, lookup_var_def, ret_pc_ok_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `dv = x` >> simp[] >> metis_tac[]
QED

Resume immutable_condition_boundary_mem[path]:
  fs[array_loop_inv_def] >>
  `k < dimword (:256)` by decide_tac >>
  `((n2w k:bytes32) = n2w (LENGTH vs)) = (k = LENGTH vs)` by simp[n2w_11] >>
  `step_inst_base (mk_inst j1 EQ [Var idx; lvo] [dv]) s =
    OK (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    simp[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def, eval_operand_def] >>
  `gas_path_mem_edge ctx func s 0
    (OK ((update_var dv (bool_to_word (k = LENGTH vs)) s) with vs_inst_idx := 1))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[mk_inst_def, get_instruction_def, is_terminator_def, inst_dload_in_section_def] >>
     disch_then irule >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func s 0 (OK mid)` >>
  `eval_operand (Var dv) mid = SOME (bool_to_word (k = LENGTH vs))` by
    simp[Abbr `mid`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst j2 JNZ [Var dv; Label exit; Label bod] []) mid =
    OK (jump_to (if k = LENGTH vs then exit else bod) mid)` by
    (drule step_jnz_behavior >>
     disch_then (qspecl_then [`exit`, `bod`, `j2`] mp_tac) >>
     Cases_on `k = LENGTH vs` >> simp[bool_to_word_def, mk_inst_def]) >>
  `mid.vs_current_bb = cond /\ mid.vs_inst_idx = 1 /\ ~mid.vs_halted` by
    simp[Abbr `mid`, update_var_def] >>
  `gas_path_mem_edge ctx func mid 0
    (OK (jump_to (if k = LENGTH vs then exit else bod) mid))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst j2 JNZ [Var dv; Label exit; Label bod] []` >>
     simp[get_instruction_def, gas_count_step_def, mem_safe_step_non_invoke,
          step_inst_non_invoke, is_terminator_def, inst_dload_in_section_def] >>
     conj_tac >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if k = LENGTH vs then exit else bod` >> simp[]) >>
  `~(jump_to (if k = LENGTH vs then exit else bod) mid).vs_halted` by
    simp[jump_to_def, Abbr `mid`, update_var_def] >>
  `jump_to (if k = LENGTH vs then exit else bod) mid =
    jump_to (if k = LENGTH vs then exit else bod)
      (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    simp[Abbr `mid`, jump_to_def, update_var_def] >>
  simp[gas_marked_path_def] >> metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
Finalise immutable_condition_boundary_mem
