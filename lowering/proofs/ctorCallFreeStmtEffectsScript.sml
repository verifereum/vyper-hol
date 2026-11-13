(* Effect and return statement opcode boundaries. *)
Theory ctorCallFreeStmtEffects
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtReturns ctorCallFreeStmtStorage ctorCallFreeStmtLogs
  ctorCallFreeABIEncode
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem call_free_stmt_assert:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e ar.
  ~supported_stmt_expr_exists constructor_call_root (Assert e ar) /\
  ~supported_stmt_expr_exists expr_shape_root (Assert e ar) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Assert e ar) st)))
Proof
  strip_tac >> drule call_free_reason_message >> disch_then assume_tac >>
  rpt gen_tac >> Cases_on `ar` >>
  simp[supported_stmt_expr_exists_def, supported_assert_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def, call_free_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      every_state_insts_fresh_label, every_state_insts_new_block,
      call_free_emit_inst, call_free_revert_with_reason]) ,
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[call_free_unwrap_value]])
QED

Theorem call_free_stmt_raise:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty rr.
  ~supported_stmt_expr_exists constructor_call_root (Raise rr) /\
  ~supported_stmt_expr_exists expr_shape_root (Raise rr) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Raise rr) st)))
Proof
  strip_tac >> drule call_free_reason_message >> disch_then assume_tac >>
  rpt gen_tac >> Cases_on `rr` >>
  simp[supported_stmt_expr_exists_def, supported_raise_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def, call_free_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      call_free_emit_inst, call_free_revert_with_reason])])
QED

Theorem call_free_stmt_log:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty eid args.
  ~supported_stmt_expr_exists constructor_call_root (Log eid args) /\
  ~supported_stmt_expr_exists expr_shape_root (Log eid args) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Log eid args) st)))
Proof
  strip_tac >> drule call_free_log_eval_all >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  `EVERY (\e. ~supported_expr_exists constructor_call_root e /\
     ~supported_expr_exists expr_shape_root e) args` by
    (gvs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  simp[Once compile_stmt_def] >>
  Cases_on `ce.ce_event_info (nsid_to_string eid)`
  >- simp[call_free_emit_inst] >>
  rename1 `SOME info` >> PairCases_on `info` >> simp[] >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, call_free_emit_inst,
      call_free_log_topic_ops, call_free_log_store_data, call_free_alloc_buffer,
      call_free_abi_encode])])
QED

Theorem call_free_stmt_return_none:
  !ce lc ty st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Return NONE) st)))
Proof
  rpt gen_tac >> qid_spec_tac `st` >> simp[Once compile_stmt_def] >>
  Cases_on `ce.ce_return_pc` >> simp[]
  >- (Cases_on `ce.ce_ctor_exit_label` >> simp[call_free_emit_inst] >>
      qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(nr, rest)` >>
      PairCases_on `rest` >> simp[Abbr `f`] >>
      ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >> simp[call_free_nonreentrant_unlock, every_state_insts_return]) >>
      simp[call_free_emit_inst]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_return_unlock, call_free_emit_op,
      call_free_emit_inst])]) >>
  Cases_on `ce.ce_ctor_exit_label` >> simp[call_free_emit_inst] >>
  qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(nr, rest)` >>
      PairCases_on `rest` >> simp[Abbr `f`] >>
  qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac >>
  simp[call_free_emit_inst] >>
  IF_CASES_TAC >> simp[call_free_nonreentrant_unlock, every_state_insts_return]
QED

Theorem call_free_stmt_return_some:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e.
  ~supported_stmt_expr_exists constructor_call_root (Return (SOME e)) /\
  ~supported_stmt_expr_exists expr_shape_root (Return (SOME e)) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Return (SOME e)) st)))
Proof
  strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[call_free_unwrap_value]) >>
  gen_tac >> Cases_on `ce.ce_return_pc` >> simp[]
  >- (rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
        gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
        CHANGED_TAC (simp[every_state_insts_return, call_free_external_return,
          call_free_nonreentrant_unlock, call_free_alloc_buffer,
          cj 1 call_free_typed_copy])])) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, call_free_external_return,
      call_free_nonreentrant_unlock, call_free_alloc_buffer, call_free_emit_op,
      call_free_internal_return_from_env, cj 1 call_free_typed_copy])])
QED
