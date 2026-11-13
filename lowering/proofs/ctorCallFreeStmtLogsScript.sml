(* Log evaluation and encoding opcode boundaries. *)
Theory ctorCallFreeStmtLogs
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  supportedExprTraverse e2eDeployDefs loweringShapeProps

Theorem call_free_log_save_arg:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_log_save_arg ce ty op es st)))
Proof
  simp[compile_log_save_arg_def] >> IF_CASES_TAC >>
  simp[every_state_insts_return, call_free_materialize_vv]
QED

Theorem call_free_encode_log_topic[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_encode_log_topic op bs st)))
Proof
  Cases_on `bs` >> simp[compile_encode_log_topic_def,
    every_state_insts_return, every_state_insts_bind, call_free_emit_op]
QED

Theorem call_free_log_topic_ops:
  !ops st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_log_topic_ops ops st)))
Proof
  Induct >> simp[compile_log_topic_ops_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_encode_log_topic, every_state_insts_return])])
QED

Theorem call_free_log_store_data:
  !ops tys ce buf off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_log_store_data ce ops tys buf off st)))
Proof
  Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, every_state_insts_return, call_free_emit_void] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_store_memory])])
QED

Theorem call_free_log_eval_all:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !es ce st.
  EVERY (\e. ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e) es ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_log_eval_all ce es st)))
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[call_free_unwrap_value]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_log_save_arg] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >>
  simp[every_state_insts_return]
QED

Theorem call_free_reason_message:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !e ce st.
  ~supported_expr_exists constructor_call_root e /\
  ~supported_expr_exists expr_shape_root e ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_reason_message ce e st)))
Proof
  strip_tac >> Cases >> simp[compile_reason_message_def] >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> simp[compile_reason_message_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_reason_message_def] >>
  Cases_on `lit` >> simp[compile_reason_message_def,
    every_state_insts_bind, every_state_insts_return, call_free_bytelike_literal]
QED
