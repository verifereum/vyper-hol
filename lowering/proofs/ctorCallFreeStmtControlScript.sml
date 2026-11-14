(* Structured control opcode boundaries, parameterized by body preservation. *)
Theory ctorCallFreeStmtControl
Ancestors
  list pair stmtLowering emitHelper context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeStmtStorage
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem opcode_every_jmp_if_not_terminated[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !lbl st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (emit_jmp_if_not_terminated lbl st)))
  )
Proof
  strip_tac >>
  gen_tac >> simp[emit_jmp_if_not_terminated_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_get] >>
  gen_tac >> IF_CASES_TAC >> simp[every_state_insts_return, opcode_every_emit_inst]
QED

Theorem opcode_every_stmt_if:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !cond b1 b2.
  (!ce lc ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty b1 st)))) /\
  (!ce lc ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty b2 st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists R (If cond b1 b2) /\
  ~supported_stmt_expr_exists expr_shape_root (If cond b1 b2) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (If cond b1 b2) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_get,
      every_state_insts_fresh_label, every_state_insts_new_block,
      opcode_every_emit_inst, (UNDISCH opcode_every_jmp_if_not_terminated)]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(UNDISCH opcode_every_unwrap_value)]])
QED

Theorem call_free_stmt_if:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !cond b1 b2.
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_stmts ce lc ty b1 st)))) /\
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_stmts ce lc ty b2 st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists expr_call_root (If cond b1 b2) /\
  ~supported_stmt_expr_exists expr_shape_root (If cond b1 b2) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (If cond b1 b2) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_if) >> simp[]
QED

Theorem opcode_every_stmt_for_range:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty start_e end_e bound body.
  (!ce lc ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists R (For id fty (Range start_e end_e) bound body) /\
  ~supported_stmt_expr_exists expr_shape_root (For id fty (Range start_e end_e) bound body) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound body) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      (UNDISCH opcode_every_declare_local), (UNDISCH opcode_every_emit_local_alloca),
      opcode_every_emit_inst, opcode_every_emit_void, opcode_every_emit_op,
      (UNDISCH opcode_every_range_bound_checks), (UNDISCH opcode_every_jmp_if_not_terminated)]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(UNDISCH opcode_every_unwrap_value)]])
  >- (Cases_on `start_e` >> simp[every_state_insts_return, opcode_every_emit_op] >>
      Cases_on `end_e` >> simp[every_state_insts_return, opcode_every_emit_op] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_end` >>
      Cases_on `lit_end` >> simp[every_state_insts_return, opcode_every_emit_op] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_start` >>
      Cases_on `lit_start` >> simp[every_state_insts_return, opcode_every_emit_op])
  >- (Cases_on `start_e` >> simp[every_state_insts_return, (UNDISCH opcode_every_range_bound_checks)] >>
      Cases_on `end_e` >> simp[every_state_insts_return, (UNDISCH opcode_every_range_bound_checks)] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_end` >>
      Cases_on `lit_end` >> simp[every_state_insts_return, (UNDISCH opcode_every_range_bound_checks)] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_start` >>
      Cases_on `lit_start` >> simp[every_state_insts_return, (UNDISCH opcode_every_range_bound_checks)]) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP vars id` >>
  Cases_on `FLOOKUP vars id` >> simp[opcode_every_emit_void] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[opcode_every_emit_void]
QED

Theorem call_free_stmt_for_range:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty start_e end_e bound body.
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists expr_call_root (For id fty (Range start_e end_e) bound body) /\
  ~supported_stmt_expr_exists expr_shape_root (For id fty (Range start_e end_e) bound body) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound body) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_for_range) >> simp[]
QED

Theorem opcode_every_stmt_for_array:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty arr bound body.
  (!ce lc ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists R (For id fty (Array arr) bound body) /\
  ~supported_stmt_expr_exists expr_shape_root (For id fty (Array arr) bound body) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Array arr) bound body) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      (UNDISCH opcode_every_declare_local), (UNDISCH opcode_every_emit_local_alloca),
      opcode_every_emit_inst, opcode_every_emit_void, opcode_every_emit_op,
      (UNDISCH opcode_every_ptr_load), (UNDISCH opcode_every_iter_elem_copy), (UNDISCH opcode_every_jmp_if_not_terminated)])]) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP vars id` >>
  Cases_on `FLOOKUP vars id` >> simp[opcode_every_emit_void] >>
  rename1 `SOME targetloc` >> Cases_on `targetloc` >>
  simp[(UNDISCH opcode_every_iter_elem_copy), opcode_every_emit_void]
QED

Theorem call_free_stmt_for_array:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty arr bound body.
  (!ce lc ty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  ~supported_stmt_expr_exists expr_call_root (For id fty (Array arr) bound body) /\
  ~supported_stmt_expr_exists expr_shape_root (For id fty (Array arr) bound body) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Array arr) bound body) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_for_array) >> simp[]
QED
