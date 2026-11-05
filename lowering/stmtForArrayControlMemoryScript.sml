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
  `gas_path_mem_edge ctx func mid 0
     (OK (jump_to (if k = n then exit_lbl else stmts_lbl) mid))` by
    (simp[gas_path_mem_edge_def] >>
     conj_tac >- simp[Abbr `mid`, update_var_def] >>
     qexists_tac `0` >>
     qexists_tac `<| bb_label := cond_lbl; bb_instructions :=
       [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |>` >>
     qexists_tac `mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []` >>
     simp[Abbr `mid`, update_var_def, mk_inst_def,
          venomInstTheory.get_instruction_def, gas_count_step_def,
          mem_safe_step_non_invoke, step_inst_non_invoke,
          step_jnz_behavior, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def,
          is_terminator_def, inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[]) >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if k = n then exit_lbl else stmts_lbl` >>
     Cases_on `k = n` >>
     simp[step_inst_base_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def]) >>
  `~(jump_to (if k = n then exit_lbl else stmts_lbl) mid).vs_halted` by
    simp[jump_to_def, Abbr `mid`, update_var_def] >>
  `jump_to (if k = n then exit_lbl else stmts_lbl) mid =
   jump_to (if k = n then exit_lbl else stmts_lbl)
     (update_var dv (bool_to_word (k = n)) cc)` by
    simp[Abbr `mid`, jump_to_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
Resume array_condition_boundary_mem[history]:
  irule alloca_history_jump >> simp[] >> qexists_tac `cc` >> simp[]
QED
Finalise array_condition_boundary_mem
