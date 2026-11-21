(* Target pointer and tuple assignment opcode boundaries. *)
Theory ctorCallFreeStmtTargets
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

(* Discharge precise opcode premises from the complement-of-seven premise. *)
val base7_tm = ``!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
  opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
  opc <> RETURNDATACOPY ==> (P:opcode -> bool) opc``;
fun b7 th = SIMP_RULE (srw_ss()) [ASSUME base7_tm, DISJ_IMP_THM, FORALL_AND_THM] th;

Theorem outcomes_free_get_target_ptr:
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
  !target ce.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_target_exists R target /\
  ~supported_target_exists extra_root target ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_get_target_ptr compile_expr ce target st)))
  )
Proof
  strip_tac >>
  strip_tac >> gen_tac >> gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >> qid_spec_tac `target` >>
  ho_match_mp_tac every_state_insts_get_target_ptr >>
  simp[(b7 outcomes_free_keccak256_key), (b7 outcomes_free_mapping_subscript), (b7 outcomes_free_alloc_buffer),
    opcode_every_emit_op, (b7 outcomes_free_array_subscript), (b7 outcomes_free_ptr_load)] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_lower_value >>
  simp[(b7 outcomes_free_unwrap_value)] >> metis_tac[]
QED

Theorem opcode_every_get_target_ptr:
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
  !target ce.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_target_exists R target /\
  ~supported_target_exists extra_root target ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_get_target_ptr compile_expr ce target st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_get_target_ptr >> simp[]
QED

Theorem outcomes_free_tuple_store_all:
  P INVALID ==>
  (
  (!bt st. ~supported_target_exists R bt /\
    ~supported_target_exists extra_root bt ==>
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
  ~supported_assignments_exists extra_root targets ==>
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

Theorem opcode_every_tuple_store_all:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!bt st. ~supported_target_exists R bt /\
    ~supported_target_exists extra_root bt ==>
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
  ~supported_assignments_exists extra_root targets ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_tuple_store_all >> simp[]
QED

Theorem outcomes_free_tuple_unpack:
  P INVALID /\ P MCOPY /\ P ALLOCA ==>
  (
  (!src tys off st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_load_all ce src tys off st)))) /\
  (!tys targets vals st.
    ~supported_assignments_exists R targets /\
    ~supported_assignments_exists extra_root targets ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))) ==>
  !ty stage targets src st.
  ~supported_assignments_exists R targets /\
  ~supported_assignments_exists extra_root targets ==>
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
    CHANGED_TAC (simp[every_state_insts_return, outcomes_free_alloc_buffer,
      opcode_every_emit_void, opcode_every_emit_inst])])
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
    ~supported_assignments_exists extra_root targets ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals st)))) ==>
  !ty stage targets src st.
  ~supported_assignments_exists R targets /\
  ~supported_assignments_exists extra_root targets ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_unpack ce ty stage targets src st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_tuple_unpack >> simp[]
QED
