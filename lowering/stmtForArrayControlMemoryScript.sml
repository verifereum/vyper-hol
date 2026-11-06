Theory stmtForArrayControlMemory
Ancestors
  stmtSimForArrayLoop stmtSimProps exprLoweringProps fragGasSeqMem
  fragGasPathMem fragExecMem allocaHistory venomInstProofs venomExecSemantics
  venomState compileEnv loweringPosts vyperState words arithmetic list
  venomInst venomExecProps memSafeRun instMemFrontier gasCount

Theorem array_condition_boundary_mem:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl st
   k es cc n dv j1 j2 exit_lbl stmts_lbl.
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st k es cc /\
  n = LENGTH vs /\ n < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  fn_inst_ids_distinct func /\ alloca_history func cc ==>
  let next = jump_to (if k = n then exit_lbl else stmts_lbl)
               (update_var dv (bool_to_word (k = n)) cc) in
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst (if k = n then exit_lbl else stmts_lbl) st k es next /\
    gas_path_mem ctx func cc 0 (OK next) /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
    next.vs_allocas = cc.vs_allocas /\ next.vs_memory = cc.vs_memory /\
    next.vs_alloca_next = cc.vs_alloca_next /\ alloca_history func next
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def,
                  finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[jump_to_def, update_var_def] >> suspend "history"
QED

Resume array_condition_boundary_mem[invariant]:
  fs[array_loop_inv_def] >>
  rename1 `eval_operand saved_base cc = SOME array_base` >>
  `stmt_state_rel ctx func cenv cx es
     (update_var dv (bool_to_word (k = n)) cc)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand saved_base (update_var dv (bool_to_word (k = n)) cc) = SOME array_base` by
    (irule eval_operand_update_other_local >> simp[]) >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
  simp[jump_to_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, ret_pc_ok_def] >>
  gvs[update_var_def, lookup_var_def, ret_pc_ok_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[] >> Cases_on `dv = x` >> simp[] >> metis_tac[]
QED
Resume array_condition_boundary_mem[path]:
  fs[array_loop_inv_def] >>
  `k < dimword (:256)` by decide_tac >>
  `((n2w k:bytes32) = n2w n) = (k = n)` by
    simp[n2w_11, LESS_MOD] >>
  `step_inst_base (mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv]) cc =
     OK (update_var dv (bool_to_word (k = n)) cc)` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def, eval_operand_def] >>
  `gas_path_mem_edge ctx func cc 0
     (OK ((update_var dv (bool_to_word (k = n)) cc) with vs_inst_idx := 1))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[mk_inst_def, venomInstTheory.get_instruction_def, is_terminator_def,
          inst_dload_in_section_def] >>
     disch_then irule >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func cc 0 (OK mid)` >>
  `eval_operand (Var dv) mid = SOME (bool_to_word (k = n))` by
    simp[Abbr `mid`, update_var_def, eval_operand_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []) mid =
     OK (jump_to (if k = n then exit_lbl else stmts_lbl) mid)` by
    (drule step_jnz_behavior >>
     disch_then (qspecl_then [`exit_lbl`, `stmts_lbl`, `j2`] mp_tac) >>
     Cases_on `k = n` >> simp[bool_to_word_def, mk_inst_def]) >>
  `mid.vs_current_bb = cond_lbl /\ mid.vs_inst_idx = 1 /\ ~mid.vs_halted` by
    simp[Abbr `mid`, update_var_def] >>
  `gas_path_mem_edge ctx func mid 0
     (OK (jump_to (if k = n then exit_lbl else stmts_lbl) mid))` by
    (simp[gas_path_mem_edge_def] >>
     qexists_tac `0` >>
     qexists_tac `mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []` >>
     simp[venomInstTheory.get_instruction_def, gas_count_step_def,
          mem_safe_step_non_invoke, step_inst_non_invoke,
          is_terminator_def, inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if k = n then exit_lbl else stmts_lbl` >> simp[]) >>
  `~(jump_to (if k = n then exit_lbl else stmts_lbl) mid).vs_halted` by
    simp[jump_to_def, Abbr `mid`, update_var_def] >>
  `jump_to (if k = n then exit_lbl else stmts_lbl) mid =
   jump_to (if k = n then exit_lbl else stmts_lbl)
     (update_var dv (bool_to_word (k = n)) cc)` by
    simp[Abbr `mid`, jump_to_def, update_var_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
Resume array_condition_boundary_mem[history]:
  irule alloca_history_jump >> simp[] >> qexists_tac `cc` >> simp[]
QED
Finalise array_condition_boundary_mem

Theorem array_increment_boundary_mem:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl
   incr_lbl st k es dd nv i1 i2 i3.
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr_lbl st k es dd /\ k < LENGTH vs /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  fn_inst_ids_distinct func /\ alloca_history func dd ==>
  let next = jump_to cond_lbl
    (update_var idx (n2w (k+1)) (update_var nv (n2w (k+1)) dd)) in
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst cond_lbl st (k+1) es next /\
    gas_path_mem ctx func dd 0 (OK next) /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x dd) /\
    next.vs_allocas = dd.vs_allocas /\ next.vs_memory = dd.vs_memory /\
    next.vs_alloca_next = dd.vs_alloca_next /\ alloca_history func next
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def,
                  finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[jump_to_def, update_var_def] >>
  irule alloca_history_jump >> simp[] >> qexists_tac `dd` >> simp[]
QED

Resume array_increment_boundary_mem[invariant]:
  fs[array_loop_inv_def] >>
  rename1 `eval_operand saved_base dd = SOME array_base` >>
  `stmt_state_rel ctx func cenv cx es
     (update_var idx (n2w (k+1)) (update_var nv (n2w (k+1)) dd))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand saved_base
     (update_var idx (n2w (k+1)) (update_var nv (n2w (k+1)) dd)) = SOME array_base` by
    (irule eval_operand_update_other_local >>
     conj_tac >- metis_tac[] >>
     irule eval_operand_update_other_local >> simp[] >> metis_tac[]) >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
  simp[jump_to_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, ret_pc_ok_def] >>
  gvs[update_var_def, lookup_var_def, ret_pc_ok_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `idx = x` >> simp[] >> Cases_on `nv = x` >> simp[] >> metis_tac[]
QED
Resume array_increment_boundary_mem[path]:
  fs[array_loop_inv_def] >>
  `step_inst_base (mk_inst i1 ADD [Var idx; Lit 1w] [nv]) dd =
     OK (update_var nv (n2w (k+1)) dd)` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def, eval_operand_def, word_add_n2w] >>
  `gas_path_mem_edge ctx func dd 0
     (OK ((update_var nv (n2w (k+1)) dd) with vs_inst_idx := 1))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[mk_inst_def, get_instruction_def, is_terminator_def, inst_dload_in_section_def] >>
     disch_then irule >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func dd 0 (OK s1)` >>
  `s1.vs_current_bb = incr_lbl /\ s1.vs_inst_idx = 1 /\ ~s1.vs_halted` by
    simp[Abbr `s1`, update_var_def] >>
  `step_inst_base (mk_inst i2 ASSIGN [Var nv] [idx]) s1 =
     OK (update_var idx (n2w (k+1)) s1)` by
    simp[step_inst_base_def, mk_inst_def, eval_operand_def,
         Abbr `s1`, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `gas_path_mem_edge ctx func s1 0
     (OK ((update_var idx (n2w (k+1)) s1) with vs_inst_idx := 2))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[mk_inst_def, get_instruction_def, is_terminator_def, inst_dload_in_section_def] >>
     disch_then irule >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func s1 0 (OK s2)` >>
  `s2.vs_current_bb = incr_lbl /\ s2.vs_inst_idx = 2 /\ ~s2.vs_halted` by
    simp[Abbr `s2`, update_var_def] >>
  `step_inst_base (mk_inst i3 JMP [Label cond_lbl] []) s2 = OK (jump_to cond_lbl s2)` by
    simp[Once step_inst_base_def, mk_inst_def] >>
  `gas_path_mem_edge ctx func s2 0 (OK (jump_to cond_lbl s2))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst i3 JMP [Label cond_lbl] []` >>
     simp[get_instruction_def, gas_count_step_def, mem_safe_step_non_invoke,
          step_inst_non_invoke, is_terminator_def, inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `cond_lbl` >> simp[]) >>
  `~(jump_to cond_lbl s2).vs_halted` by simp[jump_to_def] >>
  `jump_to cond_lbl s2 = jump_to cond_lbl
     (update_var idx (n2w (k+1)) (update_var nv (n2w (k+1)) dd))` by
    simp[Abbr `s2`, Abbr `s1`, jump_to_def, update_var_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
Finalise array_increment_boundary_mem
