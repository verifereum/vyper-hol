(* Effect and return statement opcode boundaries. *)
Theory ctorCallFreeStmtEffects
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtReturns ctorCallFreeStmtStorage ctorCallFreeStmtLogs
  ctorCallFreeABIEncode loweringFunctionOpcodes loweringCallArgsOpcodes
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

(* Discharge precise opcode premises from the complement-of-seven premise;
   c7 also discharges generator callbacks with the given precise lemmas. *)
val base7_tm = ``!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
  opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
  opc <> RETURNDATACOPY ==> (P:opcode -> bool) opc``;
fun b7 th = SIMP_RULE (srw_ss()) [ASSUME base7_tm, DISJ_IMP_THM, FORALL_AND_THM] th;
fun c7 ths th = SIMP_RULE (srw_ss()) (map b7 ths) (b7 th);

Theorem outcomes_free_positional_snapshots[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !es tys ce st.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  EVERY ($~ o supported_expr_exists R) es /\
  EVERY ($~ o supported_expr_exists expr_shape_root) es ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ext_call_args compile_expr ce [] tys es st)))
  )
Proof
  rpt strip_tac >> irule opcode_every_ext_call_args_with_snapshot >>
  simp[c7 [outcomes_free_unwrap_value, outcomes_free_alloc_buffer,
    outcomes_free_store_memory] outcomes_free_snapshot] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem outcomes_free_revert_with_custom_error[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce err st.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  EVERY ($~ o supported_expr_exists R) (custom_error_exprs err) /\
  EVERY ($~ o supported_expr_exists expr_shape_root) (custom_error_exprs err) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_revert_with_custom_error ce err st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH outcomes_free_positional_snapshots) >> strip_tac >>
  gen_tac >> Cases >> rename1 `CustomError id pos kws` >> rpt gen_tac >>
  strip_tac >> qid_spec_tac `st` >>
  simp[compile_revert_with_custom_error_def] >>
  Cases_on `ce.ce_error_info (nsid_to_string id)` >> simp[opcode_every_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac, IF_CASES_TAC,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      opcode_every_emit_inst, opcode_every_emit_void, opcode_every_emit_op,
      (b7 outcomes_free_alloc_buffer), outcomes_free_abi_encode_values_to_buf])]) >>
  metis_tac[]
QED

Theorem outcomes_free_stmt_assert:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e ar.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Assert e ar) /\
  ~supported_stmt_expr_exists expr_shape_root (Assert e ar) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assert e ar) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (b7 outcomes_free_reason_message) >> disch_then assume_tac >>
  drule (UNDISCH outcomes_free_revert_with_custom_error) >> disch_then assume_tac >>
  rpt gen_tac >> Cases_on `ar` >>
  simp[supported_stmt_expr_exists_def, supported_assert_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def, opcode_every_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      every_state_insts_fresh_label, every_state_insts_new_block,
      opcode_every_emit_inst, (c7 [outcomes_free_alloc_buffer, outcomes_free_unwrap_value] outcomes_free_compile_revert_with_reason)]) ,
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(b7 outcomes_free_unwrap_value)]]) >> metis_tac[]
QED

Theorem opcode_every_stmt_assert:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e ar.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Assert e ar) /\
  ~supported_stmt_expr_exists expr_shape_root (Assert e ar) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assert e ar) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_assert >> simp[]
QED

Theorem outcomes_free_stmt_raise:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty rr.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Raise rr) /\
  ~supported_stmt_expr_exists expr_shape_root (Raise rr) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Raise rr) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (b7 outcomes_free_reason_message) >> disch_then assume_tac >>
  drule (UNDISCH outcomes_free_revert_with_custom_error) >> disch_then assume_tac >>
  rpt gen_tac >> Cases_on `rr` >>
  simp[supported_stmt_expr_exists_def, supported_raise_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def, opcode_every_emit_inst] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      opcode_every_emit_inst, (c7 [outcomes_free_alloc_buffer, outcomes_free_unwrap_value] outcomes_free_compile_revert_with_reason)])]) >> metis_tac[]
QED

Theorem opcode_every_stmt_raise:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty rr.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Raise rr) /\
  ~supported_stmt_expr_exists expr_shape_root (Raise rr) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Raise rr) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_raise >> simp[]
QED

Theorem outcomes_free_stmt_log:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty eid args.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Log eid args) /\
  ~supported_stmt_expr_exists expr_shape_root (Log eid args) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Log eid args) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH outcomes_free_positional_snapshots) >> strip_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  `EVERY ($~ o supported_expr_exists R) args /\
   EVERY ($~ o supported_expr_exists expr_shape_root) args` by
    (gvs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  simp[Once compile_stmt_def] >>
  Cases_on `ce.ce_event_info (nsid_to_string eid)`
  >- simp[opcode_every_emit_inst] >>
  rename1 `SOME info` >> PairCases_on `info` >> simp[] >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_inst,
      outcomes_free_compile_log_saved_topics, (b7 outcomes_free_alloc_buffer),
      outcomes_free_abi_encode_values_to_buf])]) >> metis_tac[]
QED

Theorem opcode_every_stmt_log:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty eid args.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Log eid args) /\
  ~supported_stmt_expr_exists expr_shape_root (Log eid args) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Log eid args) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_log >> simp[]
QED

Theorem outcomes_free_stmt_return_none:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
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
      >- (IF_CASES_TAC >> simp[(b7 outcomes_free_nonreentrant), every_state_insts_return]) >>
      simp[opcode_every_emit_inst]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(c7 [outcomes_free_nonreentrant] (INST [``P:instruction -> bool`` |-> ``\i:instruction. (P:opcode -> bool) i.inst_opcode``] outcomes_free_return_unlock)), opcode_every_emit_op,
      opcode_every_emit_inst])]) >>
  Cases_on `ce.ce_ctor_exit_label` >> simp[opcode_every_emit_inst] >>
  qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(nr, rest)` >>
      PairCases_on `rest` >> simp[Abbr `f`] >>
  qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac >>
  simp[opcode_every_emit_inst] >>
  IF_CASES_TAC >> simp[(b7 outcomes_free_nonreentrant), every_state_insts_return]
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
  strip_tac >> match_mp_tac outcomes_free_stmt_return_none >> simp[]
QED

Theorem outcomes_free_stmt_return_some:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
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
  >- (ho_match_mp_tac every_state_insts_lower_value >>
      simp[(b7 outcomes_free_unwrap_value)] >> metis_tac[]) >>
  gen_tac >> Cases_on `ce.ce_return_pc` >> simp[]
  >- (rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
        gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
        CHANGED_TAC (simp[every_state_insts_return, (c7 [outcomes_free_nonreentrant, outcomes_free_alloc_buffer, outcomes_free_abi_encode] outcomes_free_compile_external_return),
          (b7 outcomes_free_nonreentrant), (b7 outcomes_free_alloc_buffer),
          cj 1 (b7 outcomes_free_typed_copy)])])) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, (c7 [outcomes_free_nonreentrant, outcomes_free_alloc_buffer, outcomes_free_abi_encode] outcomes_free_compile_external_return),
      (b7 outcomes_free_nonreentrant), (b7 outcomes_free_alloc_buffer), opcode_every_emit_op,
      (c7 [(c7 [outcomes_free_nonreentrant] (INST [``P:instruction -> bool`` |-> ``\i:instruction. (P:opcode -> bool) i.inst_opcode``] outcomes_free_return_unlock)), (c7 [outcomes_free_store_memory] outcomes_free_compile_internal_return)] outcomes_free_internal_return_from_env), cj 1 (b7 outcomes_free_typed_copy)])])
QED

Theorem opcode_every_stmt_return_some:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Return (SOME e)) /\
  ~supported_stmt_expr_exists expr_shape_root (Return (SOME e)) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Return (SOME e)) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_return_some >> simp[]
QED
