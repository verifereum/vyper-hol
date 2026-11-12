(* Structured control opcode boundaries, parameterized by body preservation. *)
Theory ctorCallFreeStmtControl
Ancestors
  list pair stmtLowering emitHelper context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeStmtStorage
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem call_free_jmp_if_not_terminated[local]:
  !lbl st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (emit_jmp_if_not_terminated lbl st)))
Proof
  gen_tac >> simp[emit_jmp_if_not_terminated_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_get] >>
  gen_tac >> IF_CASES_TAC >> simp[every_state_insts_return, call_free_emit_inst]
QED

Theorem call_free_stmt_if:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !cond b1 b2.
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty b1 st)))) /\
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty b2 st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists constructor_call_root (If cond b1 b2) /\
  ~supported_stmt_expr_exists expr_shape_root (If cond b1 b2) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (If cond b1 b2) st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_get,
      every_state_insts_fresh_label, every_state_insts_new_block,
      call_free_emit_inst, call_free_jmp_if_not_terminated]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[call_free_unwrap_value]])
QED

Theorem call_free_stmt_for_range:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty start_e end_e bound body.
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists constructor_call_root (For id fty (Range start_e end_e) bound body) /\
  ~supported_stmt_expr_exists expr_shape_root (For id fty (Range start_e end_e) bound body) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound body) st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      call_free_declare_local, call_free_emit_local_alloca,
      call_free_emit_inst, call_free_emit_void, call_free_emit_op,
      call_free_range_bound_checks, call_free_jmp_if_not_terminated]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[call_free_unwrap_value]])
  >- (Cases_on `start_e` >> simp[every_state_insts_return, call_free_emit_op] >>
      Cases_on `end_e` >> simp[every_state_insts_return, call_free_emit_op] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_end` >>
      Cases_on `lit_end` >> simp[every_state_insts_return, call_free_emit_op] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_start` >>
      Cases_on `lit_start` >> simp[every_state_insts_return, call_free_emit_op])
  >- (Cases_on `start_e` >> simp[every_state_insts_return, call_free_range_bound_checks] >>
      Cases_on `end_e` >> simp[every_state_insts_return, call_free_range_bound_checks] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_end` >>
      Cases_on `lit_end` >> simp[every_state_insts_return, call_free_range_bound_checks] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_start` >>
      Cases_on `lit_start` >> simp[every_state_insts_return, call_free_range_bound_checks]) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP vars id` >>
  Cases_on `FLOOKUP vars id` >> simp[call_free_emit_void] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[call_free_emit_void]
QED

Theorem call_free_stmt_for_array:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty arr bound body.
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists constructor_call_root (For id fty (Array arr) bound body) /\
  ~supported_stmt_expr_exists expr_shape_root (For id fty (Array arr) bound body) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Array arr) bound body) st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      call_free_declare_local, call_free_emit_local_alloca,
      call_free_emit_inst, call_free_emit_void, call_free_emit_op,
      call_free_ptr_load, call_free_iter_elem_copy, call_free_jmp_if_not_terminated])]) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP vars id` >>
  Cases_on `FLOOKUP vars id` >> simp[call_free_emit_void] >>
  rename1 `SOME targetloc` >> Cases_on `targetloc` >>
  simp[call_free_iter_elem_copy, call_free_emit_void]
QED
