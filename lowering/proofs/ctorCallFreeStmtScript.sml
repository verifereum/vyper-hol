(* Statement preservation assembled from expression and scaffolding boundaries. *)
Theory ctorCallFreeStmt
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeOps
  ctorCallFreeStmtReturns ctorCallFreeStmtStorage ctorCallFreeStmtLogs
  ctorCallFreeStmtTargets supportedExprTraverse supportedStmtTraverse
  e2eDeployDefs loweringShapeProps

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

