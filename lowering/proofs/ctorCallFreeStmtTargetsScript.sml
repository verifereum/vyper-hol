(* Target pointer and tuple assignment opcode boundaries. *)
Theory ctorCallFreeStmtTargets
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem call_free_get_target_ptr:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !target ce.
  ~supported_target_exists constructor_call_root target /\
  ~supported_target_exists expr_shape_root target ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_get_target_ptr compile_expr ce target st)))
Proof
  strip_tac >> gen_tac >> gen_tac >> qid_spec_tac `target` >>
  ho_match_mp_tac every_state_insts_get_target_ptr >>
  simp[call_free_keccak256_key, call_free_mapping_subscript, call_free_alloc_buffer,
    call_free_emit_op, call_free_array_subscript, call_free_ptr_load] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_lower_value >>
  simp[call_free_unwrap_value]
QED

Theorem call_free_tuple_store_all:
  (!bt st. ~supported_target_exists constructor_call_root bt /\
    ~supported_target_exists expr_shape_root bt ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_get_target_ptr compile_expr ce bt st)))) /\
  (!dst loc value prim sl dt sy da sz st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_assign_value ce dst loc value prim sl dt sy da sz st)))) /\
  (!dst value loc st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_store_at_loc ce.ce_imm_alloca dst value loc st)))) ==>
  !tys targets vals st.
  ~supported_assignments_exists constructor_call_root targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))
Proof
  strip_tac >> Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, every_state_insts_return] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def, supported_assignment_exists_def] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, call_free_emit_void])])
QED

Theorem call_free_tuple_unpack:
  (!src tys off st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_tuple_load_all ce src tys off st)))) /\
  (!tys targets vals st.
    ~supported_assignments_exists constructor_call_root targets /\
    ~supported_assignments_exists expr_shape_root targets ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))) ==>
  !ty stage targets src st.
  ~supported_assignments_exists constructor_call_root targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  simp[compile_tuple_unpack_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, call_free_alloc_buffer,
      call_free_emit_void, call_free_emit_inst])])
QED
