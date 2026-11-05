(* Construct a raw join endpoint: no assertion about continuation PHIs. *)
Theory bodyPtrBopRawArm
Ancestors
  bodyPtrBopWordPathProbe bodyPtrCtrlCases fragGasSeqPtr fragGasPathPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomInstProofs venomInst
  venomState emitHelper emitHelperProps exprLoweringProps fragExec
  compileEnv finite_map pred_set codegenRel contextCodegenRel

Theorem bop_assign_ptr_inst_ok:
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSIGN [op] [z]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem bop_emit_assign_edge:
  emit_inst ASSIGN [op] [z] sa = ((), sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id ASSIGN [op] [z]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [op] [z]) u)
    (step_taint (mk_inst sa.cs_next_id ASSIGN [op] [z]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
     SOME (mk_inst sa.cs_next_id ASSIGN [op] [z])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id ASSIGN [op] [z]) s` by
    (irule bop_assign_ptr_inst_ok >> simp[]) >>
  `(mk_inst sa.cs_next_id ASSIGN [op] [z]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst sa.cs_next_id ASSIGN [op] [z]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule straight_line_ptr_edge >>
  simp[GSYM mk_inst_def] >> disch_then drule_all >> simp[GSYM mk_inst_def]
QED

Theorem bop_emit_assign_jump_raw:
  emit_inst ASSIGN [op] [z] sa = ((), sb) /\
  emit_inst JMP [Label lbl] [] sb = ((), sc) /\
  cs_extends st0 sa /\ cs_extends sc stf /\ fn_has_code st0 stf fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn op = {} /\ op_prov G op = NONE /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id ASSIGN [op] [z]) s = OK u ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to lbl (u with vs_inst_idx := SUC s.vs_inst_idx))) /\
    op_prov G' (Var z) = NONE
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc` by
    (imp_res_tac emit_inst_extends >> simp[cs_extends_def]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  imp_res_tac emit_inst_extends >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = OK u` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure1_def, AllCaseEqs(), update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `jump_to lbl v` >>
  qexistsl_tac [`step_prov PG G (mk_inst sa.cs_next_id ASSIGN [op] [z]) u`,
    `step_taint (mk_inst sa.cs_next_id ASSIGN [op] [z]) s u tn`] >>
  reverse conj_tac
  >- (simp[op_prov_def] >> irule bop_forward_step_prov_none >>
      simp[mk_inst_def]) >>
  `gas_path_ptr D 0 ctx fn PG
     (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [op] [z]) u)
     (step_taint (mk_inst sa.cs_next_id ASSIGN [op] [z]) s u tn)
     v 0 (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [op] [z]) u)
     (step_taint (mk_inst sa.cs_next_id ASSIGN [op] [z]) s u tn)
     (OK (jump_to lbl v))` by
    (irule emit_jump_zero_path_ptr >> simp[Abbr `v`] >>
     qexistsl_tac [`sb`, `sc`] >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [op] [z]) u)
     (step_taint (mk_inst sa.cs_next_id ASSIGN [op] [z]) s u tn) (OK v)` by
    (simp[Abbr `v`] >> metis_tac[bop_emit_assign_edge]) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

(* The two emit equations are precisely st8->st9->st10 (then arm),
   or st12->st13->st14 (else arm), in compile_expr's IfExp clause.
   The child certificate must be supplied on the chosen path: the current
   body_expr_ptr_ok post does NOT itself supply op_prov G op = NONE. *)
Theorem bop_selected_arm_raw_path:
  compile_expr cenv ty arm arm_start = (vv, arm_end) /\
  compile_ifexp_arm cenv rt (lowered_value_type cenv arm) vv arm_end = (op, sa) /\
  emit_inst ASSIGN [op] [z] sa = ((), sb) /\
  emit_inst JMP [Label lbl] [] sb = ((), sc) /\
  cs_extends st0 sa /\ cs_extends sc stf /\ fn_has_code st0 stf fn /\
  gas_path_ptr D 0 ctx fn PG G0 tn0 s0 n G tn (OK s) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_taint tn op = {} /\ op_prov G op = NONE /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id ASSIGN [op] [z]) s = OK u ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G0 tn0 s0 n G' tn' (OK t) /\
    t = jump_to lbl (u with vs_inst_idx := SUC s.vs_inst_idx) /\
    t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ op_prov G' (Var z) = NONE
Proof
  strip_tac >>
  `~s.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  drule bop_emit_assign_jump_raw >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> qexistsl_tac [`G'`, `tn'`,
    `jump_to lbl (u with vs_inst_idx := SUC s.vs_inst_idx)`] >>
  simp[jump_to_def] >>
  `gas_path_ptr D 0 ctx fn PG G0 tn0 s0 (n + 0) G' tn'
     (OK (jump_to lbl (u with vs_inst_idx := SUC s.vs_inst_idx)))` by
    metis_tac[gas_path_ptr_then] >>
  gvs[jump_to_def]
QED
