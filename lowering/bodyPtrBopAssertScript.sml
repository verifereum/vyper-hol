(* Scalar assertions are terminal on failure; no suffix is executed then.
   INVALID uses the existing ptr_inst_ok_abort_zero / emit_abort_zero_path_ptr
   boundary in stmtAbortPtr rather than a duplicate lemma here. *)
Theory bodyPtrBopAssert
Ancestors
  stmtAbortPtr fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  codegenRel contextCodegenRel finite_map pred_set

Theorem bop_assert_ptr_inst_ok:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [op] []) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs(), mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem bop_assert_ghost:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) ==>
  step_prov PG G (mk_inst id opc [op] []) s = G /\
  step_taint (mk_inst id opc [op] []) s s tn = tn
Proof
  strip_tac >> gvs[] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mk_inst_def,
       set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, DRESTRICT_UNIV] >>
  `!i. ~( ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
      FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b + sz)`
    by (simp[FLOOKUP_DEF] >> metis_tac[]) >>
  simp[taint_component_equality]
QED

Theorem bop_assert_success_state:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  step_inst_base (mk_inst id opc [op] []) s = OK u ==> u = s
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem bop_assert_counted_edge:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [op] []) /\
  step_inst_base (mk_inst id opc [op] []) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `u = s` by (irule bop_assert_success_state >> metis_tac[]) >>
  qpat_x_assum `u = s` SUBST_ALL_TAC >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [op] []) s` by
    (irule bop_assert_ptr_inst_ok >> simp[]) >>
  `(mk_inst id opc [op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id opc [op] []).inst_opcode` by
    gvs[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, bop_assert_ghost]
QED

Theorem bop_assert_abort_path:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [op] []) /\
  step_inst_base (mk_inst id opc [op] []) s = Abort a t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [op] []) s` by
    (irule bop_assert_ptr_inst_ok >> simp[]) >>
  `(mk_inst id opc [op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id opc [op] []).inst_opcode` by
    gvs[mk_inst_def, is_terminator_def] >>
  drule_all gas_path_ptr_abort >> gvs[mk_inst_def]
QED

Theorem bop_assert_success_path:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [op] []) /\
  step_inst_base (mk_inst id opc [op] []) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `u = s` by (irule bop_assert_success_state >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule bop_assert_counted_edge >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn
     (u with vs_inst_idx := SUC s.vs_inst_idx) 0 G tn
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED
