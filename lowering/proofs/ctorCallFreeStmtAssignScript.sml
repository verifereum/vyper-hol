(* Assignment constructor preservation. Private scaffolding is kept here. *)
Theory ctorCallFreeStmtAssign
Ancestors
  list pair stmtLowering context compileEnv exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtStorage ctorCallFreeStmtTargets supportedExprTraverse
  supportedStmtTraverse e2eDeployDefs loweringShapeProps

(* Discharge precise opcode premises from the complement-of-seven premise;
   c7 also discharges generator callbacks with the given precise lemmas. *)
val base7_tm = ``!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
  opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
  opc <> RETURNDATACOPY ==> (P:opcode -> bool) opc``;
fun b7 th = SIMP_RULE (srw_ss()) [ASSUME base7_tm, DISJ_IMP_THM, FORALL_AND_THM] th;
fun c7 ths th = SIMP_RULE (srw_ss()) (map b7 ths) (b7 th);

Theorem outcomes_free_dynarray_append:
  (!opc. MEM opc [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD; CALLDATALOAD;
     MSTORE; SSTORE; TSTORE; ISTORE; INVALID; LT; ASSERT; ADD; MUL] ==> P opc) /\
  (!ce a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce a b ty sty st)))) /\
  (!ce src slot ty tr st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots ce src slot ty tr st)))) ==>
  !ce a b ws sz ty sty cap prim loc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_dynarray_append ce a b ws sz ty sty cap prim loc s)))
Proof
  strip_tac >> rpt gen_tac >> qid_spec_tac `s` >>
  simp[compile_dynarray_append_def] >>
  rpt (FIRST [ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
    ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `s`,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        every_state_insts_return,
      outcomes_free_ptr_load, outcomes_free_ptr_store, outcomes_free_imm_store_words]),
    first_assum irule])
QED

Theorem outcomes_free_tuple_unpack_from_expr[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) ==>
  !ty stage targets src st.
  ~supported_assignments_exists R targets /\
  ~supported_assignments_exists extra_root targets ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
  )
Proof
  strip_tac >>
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (b7 outcomes_free_tuple_unpack) >>
  simp[(c7 [outcomes_free_load_memory] outcomes_free_compile_tuple_load_all)] >>
  match_mp_tac (b7 outcomes_free_tuple_store_all) >>
  simp[(c7 [outcomes_free_alloc_buffer, outcomes_free_store_memory, outcomes_free_typed_copy, outcomes_free_copy_memory, outcomes_free_store_slots_mutual, outcomes_free_imm_store, outcomes_free_store_immutable_bytestring, outcomes_free_imm_store_words] outcomes_free_compile_assign_value), (c7 [outcomes_free_imm_store] outcomes_free_compile_store_at_loc)] >>
  metis_tac[(UNDISCH outcomes_free_get_target_ptr)]
QED

Theorem outcomes_free_stmt_annassign:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty id vt e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (AnnAssign id vt e) /\
  ~supported_stmt_expr_exists extra_root (AnnAssign id vt e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (AnnAssign id vt e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac
  >- simp[(b7 outcomes_free_emit_local_alloca)] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[every_state_insts_return, (b7 outcomes_free_unwrap_value)]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >>
  gen_tac >> Cases_on `FLOOKUP ce.ce_vars id`
  >- simp[opcode_every_emit_void] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME loc` >> Cases_on `loc` >>
  simp[opcode_every_emit_void] >>
  Cases_on `has_length_word vt /\ is_empty_value_expr e` >>
  simp[opcode_every_emit_void, (c7 [outcomes_free_alloc_buffer, outcomes_free_store_memory, outcomes_free_typed_copy, outcomes_free_copy_memory, outcomes_free_store_slots_mutual, outcomes_free_imm_store, outcomes_free_store_immutable_bytestring, outcomes_free_imm_store_words] outcomes_free_compile_assign_value)]
QED

Theorem opcode_every_stmt_annassign:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty id vt e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (AnnAssign id vt e) /\
  ~supported_stmt_expr_exists extra_root (AnnAssign id vt e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (AnnAssign id vt e) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_annassign >> simp[]
QED

Theorem outcomes_free_stmt_assign_base:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty bt e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists extra_root (Assign (BaseTarget bt) e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH outcomes_free_get_target_ptr) >> disch_then assume_tac >>
  rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >> IF_CASES_TAC >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      (c7 [outcomes_free_unwrap_value, outcomes_free_alloc_buffer, outcomes_free_store_memory] outcomes_free_snapshot), (b7 outcomes_free_unwrap_value), (c7 [outcomes_free_imm_store] outcomes_free_compile_store_at_loc)]),
    match_mp_tac (UNDISCH outcomes_free_get_target_ptr) >> simp[],
    IF_CASES_TAC >> qid_spec_tac `st`])
  >>~- ([`compile_expr _ _ _ _ (* sg *)`],
         rpt strip_tac >> first_assum irule >> metis_tac[])
  >>~- ([`compile_get_target_ptr _ _ _ _ (* sg *)`],
         rpt strip_tac >> first_assum irule >> metis_tac[]) >>
  BasicProvers.TOP_CASE_TAC >> simp[opcode_every_emit_void, (c7 [outcomes_free_alloc_buffer, outcomes_free_store_memory, outcomes_free_typed_copy, outcomes_free_copy_memory, outcomes_free_store_slots_mutual, outcomes_free_imm_store, outcomes_free_store_immutable_bytestring, outcomes_free_imm_store_words] outcomes_free_compile_assign_value)]
QED

Theorem opcode_every_stmt_assign_base:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty bt e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists extra_root (Assign (BaseTarget bt) e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_assign_base >> simp[]
QED

Theorem outcomes_free_stmt_assign_tuple:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty targets e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists extra_root (Assign (TupleTarget targets) e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assign (TupleTarget targets) e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH outcomes_free_tuple_unpack_from_expr) >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  strip_tac >> simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[(b7 outcomes_free_unwrap_value)] >> metis_tac[]
QED

Theorem opcode_every_stmt_assign_tuple:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty targets e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists extra_root (Assign (TupleTarget targets) e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assign (TupleTarget targets) e) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_assign_tuple >> simp[]
QED

Theorem outcomes_free_stmt_augassign:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty vt bt bop e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (AugAssign vt bt bop e) /\
  ~supported_stmt_expr_exists extra_root (AugAssign vt bt bop e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (AugAssign vt bt bop e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH outcomes_free_get_target_ptr) >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >> gen_tac >>
  Cases_on `dst_loc_opt` >- simp[opcode_every_emit_void] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[] >>
  simp[Once comp_bind_def, comp_return_def] >>
  simp[Once comp_bind_def, comp_return_def] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      opcode_every_emit_op, opcode_every_emit_void, (b7 outcomes_free_binop),
      (b7 outcomes_free_ptr_load), (b7 outcomes_free_ptr_store)]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(b7 outcomes_free_unwrap_value)]]) >> metis_tac[]
QED

Theorem opcode_every_stmt_augassign:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty vt bt bop e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (AugAssign vt bt bop e) /\
  ~supported_stmt_expr_exists extra_root (AugAssign vt bt bop e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (AugAssign vt bt bop e) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_augassign >> simp[]
QED

Theorem outcomes_free_stmt_append:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty target e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Append target e) /\
  ~supported_stmt_expr_exists extra_root (Append target e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Append target e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (rpt strip_tac >> irule (UNDISCH outcomes_free_get_target_ptr) >>
      conj_tac >- (qexists_tac `R` >> simp[] >> metis_tac[]) >> simp[]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >>
      simp[(b7 outcomes_free_unwrap_value)] >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (IF_CASES_TAC >> qid_spec_tac `st` >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return,
          (b7 outcomes_free_alloc_buffer), (b7 outcomes_free_store_memory)])])) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >> gen_tac >>
  simp[(c7 [outcomes_free_store_memory, outcomes_free_store_slots_mutual] outcomes_free_dynarray_append)]
QED

Theorem opcode_every_stmt_append:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty target e.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (Append target e) /\
  ~supported_stmt_expr_exists extra_root (Append target e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Append target e) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_append >> simp[]
QED
