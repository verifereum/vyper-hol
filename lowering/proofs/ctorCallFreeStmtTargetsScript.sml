(* Target pointer and tuple assignment opcode boundaries. *)
Theory ctorCallFreeStmtTargets
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

Theorem opcode_every_get_target_ptr:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !target ce.
  ~supported_target_exists R target /\
  ~supported_target_exists expr_shape_root target ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_get_target_ptr compile_expr ce target st)))
  )
Proof
  strip_tac >>
  strip_tac >> gen_tac >> gen_tac >> qid_spec_tac `target` >>
  ho_match_mp_tac every_state_insts_get_target_ptr >>
  simp[(UNDISCH opcode_every_keccak256_key), (UNDISCH opcode_every_mapping_subscript), (UNDISCH opcode_every_alloc_buffer),
    opcode_every_emit_op, (UNDISCH opcode_every_array_subscript), (UNDISCH opcode_every_ptr_load)] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_lower_value >>
  simp[(UNDISCH opcode_every_unwrap_value)]
QED

Theorem call_free_get_target_ptr:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !target ce.
  ~supported_target_exists expr_call_root target /\
  ~supported_target_exists expr_shape_root target ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_get_target_ptr compile_expr ce target st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_get_target_ptr) >> simp[]
QED

Theorem opcode_every_tuple_store_all:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!bt st. ~supported_target_exists R bt /\
    ~supported_target_exists expr_shape_root bt ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_get_target_ptr compile_expr ce bt st)))) /\
  (!dst loc value prim sl dt sy sz st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_assign_value ce dst loc value prim sl dt sy sz st)))) /\
  (!dst value loc st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_at_loc ce.ce_imm_alloca dst value loc st)))) ==>
  !tys targets vals st.
  ~supported_assignments_exists R targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))
  )
Proof
  strip_tac >>
  strip_tac >> Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, every_state_insts_return] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def, supported_assignment_exists_def] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_void])])
QED

Theorem call_free_tuple_store_all:
  (!bt st. ~supported_target_exists expr_call_root bt /\
    ~supported_target_exists expr_shape_root bt ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_get_target_ptr compile_expr ce bt st)))) /\
  (!dst loc value prim sl dt sy sz st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_assign_value ce dst loc value prim sl dt sy sz st)))) /\
  (!dst value loc st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_store_at_loc ce.ce_imm_alloca dst value loc st)))) ==>
  !tys targets vals st.
  ~supported_assignments_exists expr_call_root targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_tuple_store_all) >> simp[]
QED

Theorem opcode_every_tuple_unpack:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!src tys off st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_load_all ce src tys off st)))) /\
  (!tys targets vals st.
    ~supported_assignments_exists R targets /\
    ~supported_assignments_exists expr_shape_root targets ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))) ==>
  !ty stage targets src st.
  ~supported_assignments_exists R targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  simp[compile_tuple_unpack_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, (UNDISCH opcode_every_alloc_buffer),
      opcode_every_emit_void, opcode_every_emit_inst])])
QED

Theorem call_free_tuple_unpack:
  (!src tys off st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_tuple_load_all ce src tys off st)))) /\
  (!tys targets vals st.
    ~supported_assignments_exists expr_call_root targets /\
    ~supported_assignments_exists expr_shape_root targets ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))) ==>
  !ty stage targets src st.
  ~supported_assignments_exists expr_call_root targets /\
  ~supported_assignments_exists expr_shape_root targets ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_tuple_unpack) >> simp[]
QED
