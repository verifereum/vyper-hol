(* Log evaluation and encoding opcode boundaries. *)
Theory ctorCallFreeStmtLogs
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  supportedExprTraverse e2eDeployDefs loweringShapeProps

Theorem opcode_every_log_save_arg:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_save_arg ce ty op es st)))
  )
Proof
  strip_tac >>
  simp[compile_log_save_arg_def] >> IF_CASES_TAC >>
  simp[every_state_insts_return, (UNDISCH opcode_every_materialize_vv)]
QED

Theorem call_free_log_save_arg:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_log_save_arg ce ty op es st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_log_save_arg) >> simp[]
QED

Theorem opcode_every_encode_log_topic[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_encode_log_topic op bs st)))
  )
Proof
  strip_tac >>
  Cases_on `bs` >> simp[compile_encode_log_topic_def,
    every_state_insts_return, every_state_insts_bind, opcode_every_emit_op]
QED

Theorem opcode_every_log_topic_ops:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !ops st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_topic_ops ops st)))
  )
Proof
  strip_tac >>
  Induct >> simp[compile_log_topic_ops_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_encode_log_topic), every_state_insts_return])])
QED

Theorem call_free_log_topic_ops:
  !ops st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_log_topic_ops ops st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_log_topic_ops) >> simp[]
QED

Theorem opcode_every_log_store_data:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !ops tys ce buf off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_store_data ce ops tys buf off st)))
  )
Proof
  strip_tac >>
  Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, every_state_insts_return, opcode_every_emit_void] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, (UNDISCH opcode_every_store_memory)])])
QED

Theorem call_free_log_store_data:
  !ops tys ce buf off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_log_store_data ce ops tys buf off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_log_store_data) >> simp[]
QED

Theorem opcode_every_log_eval_all:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !es ce st.
  EVERY (\e. ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e) es ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_eval_all ce es st)))
  )
Proof
  strip_tac >>
  strip_tac >> Induct >> simp[compile_log_eval_all_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[(UNDISCH opcode_every_unwrap_value)]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[(UNDISCH opcode_every_log_save_arg)] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >>
  simp[every_state_insts_return]
QED

Theorem call_free_log_eval_all:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !es ce st.
  EVERY (\e. ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e) es ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_log_eval_all ce es st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_log_eval_all) >> simp[]
QED

Theorem opcode_every_reason_message:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !e ce st.
  ~supported_expr_exists R e /\
  ~supported_expr_exists expr_shape_root e ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_reason_message ce e st)))
  )
Proof
  strip_tac >>
  strip_tac >> Cases >> simp[compile_reason_message_def] >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> simp[compile_reason_message_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_reason_message_def] >>
  Cases_on `lit` >> simp[compile_reason_message_def,
    every_state_insts_bind, every_state_insts_return, (UNDISCH opcode_every_bytelike_literal)]
QED

Theorem call_free_reason_message:
  (!ce ty e st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !e ce st.
  ~supported_expr_exists expr_call_root e /\
  ~supported_expr_exists expr_shape_root e ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_reason_message ce e st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] opcode_every_reason_message) >> simp[]
QED
