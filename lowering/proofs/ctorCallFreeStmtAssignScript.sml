(* Assignment constructor preservation. Private scaffolding is kept here. *)
Theory ctorCallFreeStmtAssign
Ancestors
  list pair stmtLowering context compileEnv exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtStorage ctorCallFreeStmtTargets supportedExprTraverse
  supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem call_free_snapshot_vv[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_snapshot_vv ce copy vv st)))
Proof
  qid_spec_tac `st` >> simp[compile_snapshot_vv_def] >>
  rpt (FIRST [IF_CASES_TAC >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_bind >> conj_tac, gen_tac,
    CHANGED_TAC (simp[call_free_unwrap_value, call_free_materialize_vv,
      every_state_insts_return])])
QED

Theorem call_free_dynarray_append[local]:
  load_op <> RETURNDATACOPY /\ load_op <> INVOKE /\
  store_op <> RETURNDATACOPY /\ store_op <> INVOKE ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_dynarray_append ce base_op value ws sz dt sy cap prim load_op store_op st)))
Proof
  strip_tac >> simp[compile_dynarray_append_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_store_memory, call_free_word_copy_loop, every_state_insts_return])])
QED

Theorem call_free_tuple_unpack_from_expr[local]:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce ty stage targets src st.
  ~supported_assignments_exists constructor_call_root targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
Proof
  strip_tac >> gen_tac >>
  match_mp_tac call_free_tuple_unpack >>
  simp[call_free_tuple_load_all] >>
  match_mp_tac call_free_tuple_store_all >>
  simp[call_free_assign_value, call_free_store_at_loc] >>
  metis_tac[call_free_get_target_ptr]
QED

Theorem call_free_stmt_annassign:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty id vt e.
  ~supported_stmt_expr_exists constructor_call_root (AnnAssign id vt e) /\
  ~supported_stmt_expr_exists expr_shape_root (AnnAssign id vt e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (AnnAssign id vt e) st)))
Proof
  strip_tac >> rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac
  >- simp[call_free_emit_local_alloca] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[every_state_insts_return, call_free_unwrap_value]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >>
  gen_tac >> Cases_on `FLOOKUP ce.ce_vars id`
  >- simp[call_free_emit_void] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME loc` >> Cases_on `loc` >>
  simp[call_free_emit_void] >>
  Cases_on `has_length_word vt /\ is_empty_value_expr e` >>
  simp[call_free_emit_void, call_free_assign_value]
QED

Theorem call_free_stmt_assign_base:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty bt e.
  ~supported_stmt_expr_exists constructor_call_root (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists expr_shape_root (Assign (BaseTarget bt) e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) st)))
Proof
  strip_tac >> drule call_free_get_target_ptr >> disch_then assume_tac >>
  rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >> IF_CASES_TAC >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      call_free_snapshot_vv, call_free_unwrap_value, call_free_store_at_loc]),
    match_mp_tac call_free_get_target_ptr >> simp[],
    IF_CASES_TAC >> qid_spec_tac `st`]) >>
  Cases_on `dst_loc_opt` >> simp[call_free_emit_void, call_free_assign_value]
QED

Theorem call_free_stmt_assign_tuple:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty targets e.
  ~supported_stmt_expr_exists constructor_call_root (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists expr_shape_root (Assign (TupleTarget targets) e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Assign (TupleTarget targets) e) st)))
Proof
  strip_tac >> drule call_free_tuple_unpack_from_expr >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  strip_tac >> simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_unwrap_value] >> simp[]
QED

Theorem call_free_stmt_augassign:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty vt bt bop e.
  ~supported_stmt_expr_exists constructor_call_root (AugAssign vt bt bop e) /\
  ~supported_stmt_expr_exists expr_shape_root (AugAssign vt bt bop e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (AugAssign vt bt bop e) st)))
Proof
  strip_tac >> drule call_free_get_target_ptr >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >> gen_tac >>
  Cases_on `dst_loc_opt` >- simp[call_free_emit_void] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[] >>
  simp[Once comp_bind_def, comp_return_def] >>
  simp[Once comp_bind_def, comp_return_def] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      call_free_emit_op, call_free_emit_void, call_free_binop]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[call_free_unwrap_value]])
QED

Theorem call_free_stmt_append:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty target e.
  ~supported_stmt_expr_exists constructor_call_root (Append target e) /\
  ~supported_stmt_expr_exists expr_shape_root (Append target e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_stmt ce lc ty (Append target e) st)))
Proof
  strip_tac >> rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[call_free_unwrap_value]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (IF_CASES_TAC >> qid_spec_tac `st` >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return,
          call_free_alloc_buffer, call_free_store_memory])])) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >> gen_tac >>
  match_mp_tac call_free_dynarray_append >>
  Cases_on `infer_array_location ce (target_to_expr target)` >>
  simp[load_opc_for_def, store_opc_for_def]
QED
