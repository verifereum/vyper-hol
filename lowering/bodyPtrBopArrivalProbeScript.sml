(* A cursor can be revisited after continuation code changes a result.
   This tests the path interface, not the full body simulation premises. *)
Theory bodyPtrBopArrivalProbe
Ancestors fragGasPath gasCount venomExecSemantics venomState venomInst
  finite_map list arithmetic

Theorem bop_arrival_assign_edge:
  ~s.vs_halted /\ s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst 0 ASSIGN [Lit 1w] ["result"]; mk_inst 1 JMP [Label lbl] []] ==>
  gas_path_edge ctx fn s 0
    (OK ((update_var "result" 1w s) with vs_inst_idx := 1))
Proof
  strip_tac >> simp[gas_path_edge_def] >>
  qexistsl_tac [`0`, `mk_inst 0 ASSIGN [Lit 1w] ["result"]`] >>
  simp[get_instruction_def, mk_inst_def, Once step_inst_def,
       step_inst_base_opcode_eqs, eval_operand_def, gas_count_step_def,
       is_terminator_def, update_var_def]
QED

Theorem bop_arrival_jump_edge:
  ~s.vs_halted /\ s.vs_current_bb = lbl /\ s.vs_inst_idx = 1 /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst 0 ASSIGN [Lit 1w] ["result"]; mk_inst 1 JMP [Label lbl] []] ==>
  gas_path_edge ctx fn s 0 (OK (jump_to lbl s))
Proof
  strip_tac >> simp[gas_path_edge_def] >>
  qexistsl_tac [`0`, `mk_inst 1 JMP [Label lbl] []`] >>
  simp[get_instruction_def, mk_inst_def, Once step_inst_def,
       step_inst_base_opcode_eqs, gas_count_step_def, is_terminator_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `lbl` >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem bop_arrival_cursor_revisit:
  ~s.vs_halted /\ s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\
  lookup_var "result" s = SOME 0w /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst 0 ASSIGN [Lit 1w] ["result"]; mk_inst 1 JMP [Label lbl] []] ==>
  ?t u. gas_path_edge ctx fn s 0 (OK u) /\ u.vs_inst_idx = 1 /\
    gas_path_edge ctx fn u 0 (OK t) /\
    gas_path ctx fn s 0 (OK t) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    lookup_var "result" t = SOME 1w /\ t <> s
Proof
  strip_tac >>
  qexistsl_tac [`jump_to lbl ((update_var "result" 1w s) with vs_inst_idx := 1)`,
    `(update_var "result" 1w s) with vs_inst_idx := 1`] >>
  `gas_path_edge ctx fn s 0
    (OK ((update_var "result" 1w s) with vs_inst_idx := 1))` by
    (irule bop_arrival_assign_edge >> simp[] >> metis_tac[]) >>
  `gas_path_edge ctx fn ((update_var "result" 1w s) with vs_inst_idx := 1) 0
    (OK (jump_to lbl ((update_var "result" 1w s) with vs_inst_idx := 1)))` by
    (irule bop_arrival_jump_edge >> simp[update_var_def] >> metis_tac[]) >>
  `gas_path ctx fn s 0
    (OK (jump_to lbl ((update_var "result" 1w s) with vs_inst_idx := 1)))` by
    metis_tac[gas_path_rules, ADD_CLAUSES, gas_path_edge_normal] >>
  simp[update_var_def, jump_to_def, lookup_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[lookup_var_def, venom_state_component_equality, FLOOKUP_UPDATE] >>
  qpat_x_assum `_ |+ _ = _` (mp_tac o Q.AP_TERM `\m. FLOOKUP m "result"`) >>
  simp[FLOOKUP_UPDATE]
QED
