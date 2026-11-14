(* Assignment constructor preservation. Private scaffolding is kept here. *)
Theory ctorCallFreeStmtAssign
Ancestors
  list pair stmtLowering context compileEnv exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtStorage ctorCallFreeStmtTargets supportedExprTraverse
  supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem opcode_every_dynarray_append[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  P load_op /\
  P store_op ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_dynarray_append ce base_op value ws sz dt sy cap prim load_op store_op st)))
  )
Proof
  strip_tac >>
  strip_tac >> simp[compile_dynarray_append_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_store_memory), (UNDISCH opcode_every_word_copy_loop), every_state_insts_return,
      cj 1 (UNDISCH opcode_every_store_slots)])])
QED

Theorem opcode_every_tuple_unpack_from_expr[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce ty stage targets src st.
  ~supported_assignments_exists R targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
  )
Proof
  strip_tac >>
  strip_tac >> gen_tac >>
  match_mp_tac (UNDISCH opcode_every_tuple_unpack) >>
  simp[(UNDISCH opcode_every_tuple_load_all)] >>
  match_mp_tac (UNDISCH opcode_every_tuple_store_all) >>
  simp[(UNDISCH opcode_every_assign_value), (UNDISCH opcode_every_store_at_loc)] >>
  metis_tac[(UNDISCH opcode_every_get_target_ptr)]
QED

Theorem opcode_every_stmt_annassign:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty id vt e.
  ~supported_stmt_expr_exists R (AnnAssign id vt e) /\
  ~supported_stmt_expr_exists expr_shape_root (AnnAssign id vt e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (AnnAssign id vt e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac
  >- simp[(UNDISCH opcode_every_emit_local_alloca)] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[every_state_insts_return, (UNDISCH opcode_every_unwrap_value)]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >>
  gen_tac >> Cases_on `FLOOKUP ce.ce_vars id`
  >- simp[opcode_every_emit_void] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME loc` >> Cases_on `loc` >>
  simp[opcode_every_emit_void] >>
  Cases_on `has_length_word vt /\ is_empty_value_expr e` >>
  simp[opcode_every_emit_void, (UNDISCH opcode_every_assign_value)]
QED

Theorem call_free_stmt_annassign:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty id vt e.
  ~supported_stmt_expr_exists expr_call_root (AnnAssign id vt e) /\
  ~supported_stmt_expr_exists expr_shape_root (AnnAssign id vt e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (AnnAssign id vt e) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_annassign) >> simp[]
QED

Theorem opcode_every_stmt_assign_base:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty bt e.
  ~supported_stmt_expr_exists R (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists expr_shape_root (Assign (BaseTarget bt) e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_get_target_ptr) >> disch_then assume_tac >>
  rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >> IF_CASES_TAC >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return,
      (UNDISCH opcode_every_snapshot_vv), (UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_store_at_loc)]),
    match_mp_tac (UNDISCH opcode_every_get_target_ptr) >> simp[],
    IF_CASES_TAC >> qid_spec_tac `st`]) >>
  Cases_on `dst_loc_opt` >> simp[opcode_every_emit_void, (UNDISCH opcode_every_assign_value)]
QED

Theorem call_free_stmt_assign_base:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty bt e.
  ~supported_stmt_expr_exists expr_call_root (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists expr_shape_root (Assign (BaseTarget bt) e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_assign_base) >> simp[]
QED

Theorem opcode_every_stmt_assign_tuple:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty targets e.
  ~supported_stmt_expr_exists R (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists expr_shape_root (Assign (TupleTarget targets) e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Assign (TupleTarget targets) e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_tuple_unpack_from_expr) >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  strip_tac >> simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[(UNDISCH opcode_every_unwrap_value)] >> simp[]
QED

Theorem call_free_stmt_assign_tuple:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty targets e.
  ~supported_stmt_expr_exists expr_call_root (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists expr_shape_root (Assign (TupleTarget targets) e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Assign (TupleTarget targets) e) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_assign_tuple) >> simp[]
QED

Theorem opcode_every_stmt_augassign:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty vt bt bop e.
  ~supported_stmt_expr_exists R (AugAssign vt bt bop e) /\
  ~supported_stmt_expr_exists expr_shape_root (AugAssign vt bt bop e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (AugAssign vt bt bop e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> drule (UNDISCH opcode_every_get_target_ptr) >> disch_then assume_tac >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
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
      opcode_every_emit_op, opcode_every_emit_void, (UNDISCH opcode_every_binop)]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(UNDISCH opcode_every_unwrap_value)]])
QED

Theorem call_free_stmt_augassign:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty vt bt bop e.
  ~supported_stmt_expr_exists expr_call_root (AugAssign vt bt bop e) /\
  ~supported_stmt_expr_exists expr_shape_root (AugAssign vt bt bop e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (AugAssign vt bt bop e) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_augassign) >> simp[]
QED

Theorem opcode_every_stmt_append:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty target e.
  ~supported_stmt_expr_exists R (Append target e) /\
  ~supported_stmt_expr_exists expr_shape_root (Append target e) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (Append target e) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  `!l. load_opc_for l <> RETURNDATACOPY /\ load_opc_for l <> INVOKE /\ load_opc_for l <> CREATE /\ load_opc_for l <> CREATE2 /\
       store_opc_for l <> RETURNDATACOPY /\ store_opc_for l <> INVOKE /\ store_opc_for l <> CREATE /\ store_opc_for l <> CREATE2` by
    (Cases >> simp[load_opc_for_def, store_opc_for_def]) >>
  simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (rpt strip_tac >> irule (UNDISCH opcode_every_get_target_ptr) >>
      conj_tac >- (qexists_tac `R` >> simp[]) >> simp[]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[(UNDISCH opcode_every_unwrap_value)]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (IF_CASES_TAC >> qid_spec_tac `st` >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return,
          (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_store_memory)])])) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_return] >> gen_tac >>
  match_mp_tac (UNDISCH opcode_every_dynarray_append) >> simp[]
QED

Theorem call_free_stmt_append:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty target e.
  ~supported_stmt_expr_exists expr_call_root (Append target e) /\
  ~supported_stmt_expr_exists expr_shape_root (Append target e) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmt ce lc ty (Append target e) st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_stmt_append) >> simp[]
QED
