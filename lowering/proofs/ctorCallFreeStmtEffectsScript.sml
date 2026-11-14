(* Effect and return statement opcode boundaries. *)
Theory ctorCallFreeStmtEffects
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtReturns ctorCallFreeStmtStorage ctorCallFreeStmtLogs
  ctorCallFreeABIEncode
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem opcode_every_custom_error_store_args[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !es tys ce dst off st.
  EVERY ($~ o supported_expr_exists R) es /\
  EVERY ($~ o supported_expr_exists expr_shape_root) es ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_custom_error_store_args ce es tys dst off st)))
  )
Proof
  strip_tac >>
  strip_tac >> Induct >> Cases_on `tys` >>
  simp[compile_custom_error_store_args_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[COND_RATOR, COND_RAND, every_state_insts_return,
      opcode_every_emit_op, (UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_store_memory)])])
QED

Theorem opcode_every_revert_with_custom_error[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce err st.
  EVERY ($~ o supported_expr_exists R) (custom_error_exprs err) /\
  EVERY ($~ o supported_expr_exists expr_shape_root) (custom_error_exprs err) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_revert_with_custom_error ce err st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_custom_error_store_args) >> strip_tac >>
  gen_tac >> Cases >> rename1 `CustomError id pos kws` >> rpt gen_tac >>
  strip_tac >> qid_spec_tac `st` >>
  simp[compile_revert_with_custom_error_def] >>
  Cases_on `ce.ce_error_info (nsid_to_string id)` >> simp[opcode_every_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac, IF_CASES_TAC,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      opcode_every_emit_inst, opcode_every_emit_void, opcode_every_emit_op,
      (UNDISCH opcode_every_alloc_buffer), cj 2 (UNDISCH opcode_every_abi_encode)])])
QED

Theorem opcode_every_stmt_assert:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e ar.
  ~supported_stmt_expr_exists R (Assert e ar) /\
  ~supported_stmt_expr_exists expr_shape_root (Assert e ar) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assert e ar) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_reason_message) >> disch_then assume_tac >>
  drule (UNDISCH opcode_every_revert_with_custom_error) >> disch_then assume_tac >>
  rpt gen_tac >> Cases_on `ar` >>
  simp[supported_stmt_expr_exists_def, supported_assert_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def, opcode_every_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      every_state_insts_fresh_label, every_state_insts_new_block,
      opcode_every_emit_inst, (UNDISCH opcode_every_revert_with_reason)]) ,
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(UNDISCH opcode_every_unwrap_value)]])
QED

Theorem call_free_stmt_assert:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e ar.
  ~supported_stmt_expr_exists expr_call_root (Assert e ar) /\
  ~supported_stmt_expr_exists expr_shape_root (Assert e ar) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Assert e ar) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_assert) >> simp[]
QED

Theorem opcode_every_stmt_raise:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty rr.
  ~supported_stmt_expr_exists R (Raise rr) /\
  ~supported_stmt_expr_exists expr_shape_root (Raise rr) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Raise rr) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_reason_message) >> disch_then assume_tac >>
  drule (UNDISCH opcode_every_revert_with_custom_error) >> disch_then assume_tac >>
  rpt gen_tac >> Cases_on `rr` >>
  simp[supported_stmt_expr_exists_def, supported_raise_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def, opcode_every_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      opcode_every_emit_inst, (UNDISCH opcode_every_revert_with_reason)])])
QED

Theorem call_free_stmt_raise:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty rr.
  ~supported_stmt_expr_exists expr_call_root (Raise rr) /\
  ~supported_stmt_expr_exists expr_shape_root (Raise rr) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Raise rr) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_raise) >> simp[]
QED

Theorem opcode_every_stmt_log:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty eid args.
  ~supported_stmt_expr_exists R (Log eid args) /\
  ~supported_stmt_expr_exists expr_shape_root (Log eid args) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Log eid args) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_log_eval_all) >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  `EVERY (\e. ~supported_expr_exists R e /\
     ~supported_expr_exists expr_shape_root e) args` by
    (gvs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  simp[Once compile_stmt_def] >>
  Cases_on `ce.ce_event_info (nsid_to_string eid)`
  >- simp[opcode_every_emit_inst] >>
  rename1 `SOME info` >> PairCases_on `info` >> simp[] >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_inst,
      (UNDISCH opcode_every_log_topic_ops), (UNDISCH opcode_every_log_store_data), (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_abi_encode)])])
QED

Theorem call_free_stmt_log:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty eid args.
  ~supported_stmt_expr_exists expr_call_root (Log eid args) /\
  ~supported_stmt_expr_exists expr_shape_root (Log eid args) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Log eid args) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_log) >> simp[]
QED

Theorem opcode_every_stmt_return_none:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !ce lc ty st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Return NONE) st)))
  )
Proof
  strip_tac >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[Once compile_stmt_def] >>
  Cases_on `ce.ce_return_pc` >> simp[]
  >- (Cases_on `ce.ce_ctor_exit_label` >> simp[opcode_every_emit_inst] >>
      qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(nr, rest)` >>
      PairCases_on `rest` >> simp[Abbr `f`] >>
      ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >> simp[(UNDISCH opcode_every_nonreentrant_unlock), every_state_insts_return]) >>
      simp[opcode_every_emit_inst]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_return_unlock), opcode_every_emit_op,
      opcode_every_emit_inst])]) >>
  Cases_on `ce.ce_ctor_exit_label` >> simp[opcode_every_emit_inst] >>
  qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(nr, rest)` >>
      PairCases_on `rest` >> simp[Abbr `f`] >>
  qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac >>
  simp[opcode_every_emit_inst] >>
  IF_CASES_TAC >> simp[(UNDISCH opcode_every_nonreentrant_unlock), every_state_insts_return]
QED

Theorem call_free_stmt_return_none:
  !ce lc ty st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Return NONE) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_stmt_return_none) >> simp[]
QED

Theorem opcode_every_stmt_return_some:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e.
  ~supported_stmt_expr_exists R (Return (SOME e)) /\
  ~supported_stmt_expr_exists expr_shape_root (Return (SOME e)) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Return (SOME e)) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[(UNDISCH opcode_every_unwrap_value)]) >>
  gen_tac >> Cases_on `ce.ce_return_pc` >> simp[]
  >- (rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
        gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
        CHANGED_TAC (simp[every_state_insts_return, (UNDISCH opcode_every_external_return),
          (UNDISCH opcode_every_nonreentrant_unlock), (UNDISCH opcode_every_alloc_buffer),
          cj 1 (UNDISCH opcode_every_typed_copy)])])) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, (UNDISCH opcode_every_external_return),
      (UNDISCH opcode_every_nonreentrant_unlock), (UNDISCH opcode_every_alloc_buffer), opcode_every_emit_op,
      (UNDISCH opcode_every_internal_return_from_env), cj 1 (UNDISCH opcode_every_typed_copy)])])
QED

Theorem call_free_stmt_return_some:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e.
  ~supported_stmt_expr_exists expr_call_root (Return (SOME e)) /\
  ~supported_stmt_expr_exists expr_shape_root (Return (SOME e)) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Return (SOME e)) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_return_some) >> simp[]
QED
