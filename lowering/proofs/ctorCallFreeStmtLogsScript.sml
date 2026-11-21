(* Log evaluation and encoding opcode boundaries. *)
Theory ctorCallFreeStmtLogs
Ancestors
  list pair stmtLowering context exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  supportedExprTraverse e2eDeployDefs loweringShapeProps

(* Discharge precise opcode premises from the complement-of-seven premise;
   c7 also discharges generator callbacks with the given precise lemmas. *)
val base7_tm = ``!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
  opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
  opc <> RETURNDATACOPY ==> (P:opcode -> bool) opc``;
fun b7 th = SIMP_RULE (srw_ss()) [ASSUME base7_tm, DISJ_IMP_THM, FORALL_AND_THM] th;
fun c7 ths th = SIMP_RULE (srw_ss()) (map b7 ths) (b7 th);

Theorem outcomes_free_compile_log_save_arg:
  (!ce ty vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_materialize_vv ce ty vv s)))) ==>
  !ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_save_arg ce ty op es s)))
Proof
  rpt strip_tac >> simp[compile_log_save_arg_def] >>
  IF_CASES_TAC >- simp[every_state_insts_return] >> first_x_assum irule >> simp[]
QED

Theorem opcode_every_log_save_arg:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_save_arg ce ty op es st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_log_save_arg >>
  simp[UNDISCH opcode_every_materialize_vv]
QED

Theorem outcomes_free_encode_log_topic:
  P ADD /\ P MLOAD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_encode_log_topic src bytestring s)))
Proof
  strip_tac >> Cases_on `bytestring` >>
  simp[compile_encode_log_topic_def, every_state_insts_return] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst] >> rpt strip_tac >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_log_saved_topics:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (!ops ce s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_saved_topics ce ops s))))
Proof
  strip_tac >> Induct >> simp[compile_log_saved_topics_def, every_state_insts_return] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_log_saved_topics_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac, gen_tac,
    CHANGED_TAC (simp[every_state_insts_return, b7 outcomes_free_unwrap_value,
      b7 outcomes_free_encode_log_topic])]) >> metis_tac[]
QED

Theorem outcomes_free_compile_log_topic_ops:
  (!op bs s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_encode_log_topic op bs s)))) ==>
  !ops s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_topic_ops ops s)))
Proof
  strip_tac >> Induct >> simp[compile_log_topic_ops_def, every_state_insts_return] >>
  gen_tac >> ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_bind >> simp[every_state_insts_return]
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
  strip_tac >> match_mp_tac outcomes_free_compile_log_topic_ops >>
  rpt strip_tac >> irule outcomes_free_encode_log_topic >> simp[]
QED

Theorem outcomes_free_compile_log_store_data:
  P ADD /\ P INVALID /\
  (!ce v dst ty src s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_store_memory ce v dst ty src s)))) ==>
  !ops ce tys buf off s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_store_data ce ops tys buf off s)))
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `tys` >>
  simp[compile_log_store_data_def, every_state_insts_return]
  >- metis_tac[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
  >- metis_tac[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  qid_spec_tac `s` >> ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac
  >- metis_tac[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  gen_tac >> ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> simp[]
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
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule outcomes_free_compile_log_store_data >>
  simp[UNDISCH opcode_every_store_memory]
QED

Theorem every_state_insts_log_eval_all:
  (!vv s. EVERY P (state_insts s) ==>
     EVERY P (state_insts (SND (unwrap_value ce vv s)))) /\
  (!ty op es s. EVERY P (state_insts s) ==>
     EVERY P (state_insts (SND (compile_log_save_arg ce ty op es s)))) ==>
  !es. EVERY (\e. !ty s. EVERY P (state_insts s) ==>
      EVERY P (state_insts (SND (compile_expr ce ty e s)))) es ==>
  !s. EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (compile_log_eval_all ce es s)))
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >>
  simp[every_state_insts_return]
QED

Theorem outcomes_free_log_eval_all:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT]
    ==> P opc) ==>
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
  !es ce st.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  EVERY (\e. ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e) es ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_eval_all ce es st)))
  )
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  irule every_state_insts_log_eval_all >>
  `!ce ty vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_materialize_vv ce ty vv s)))`
    by (rpt strip_tac >> irule outcomes_free_materialize_vv >>
        simp[DISJ_IMP_THM, outcomes_free_alloc_buffer,
             outcomes_free_unwrap_value, outcomes_free_store_memory]) >>
  drule outcomes_free_compile_log_save_arg >> strip_tac >>
  simp[DISJ_IMP_THM, outcomes_free_unwrap_value] >>
  simp[Once EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!ce ty e st. _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >> fs[EVERY_MEM]
QED

Theorem opcode_every_log_eval_all:
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
  !es ce st.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  EVERY (\e. ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e) es ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_log_eval_all ce es st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_log_eval_all >> simp[DISJ_IMP_THM]
QED

Theorem every_state_insts_reason_message:
  !ce e.
  (!ty s. EVERY P (state_insts s) ==>
     EVERY P (state_insts (SND (compile_expr ce ty e s)))) /\
  (!bs n s. EVERY P (state_insts s) ==>
     EVERY P (state_insts (SND (compile_bytelike_literal bs n s)))) ==>
  !s. EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (compile_reason_message ce e s)))
Proof
  recInduct compile_reason_message_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> simp[compile_reason_message_def] >>
  ho_match_mp_tac every_state_insts_bind >> simp[every_state_insts_return]
QED

Theorem outcomes_free_reason_message:
  P ALLOCA /\ P ADD /\ P MSTORE ==>
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
  !e ce st.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_expr_exists R e /\
  ~supported_expr_exists expr_shape_root e ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_reason_message ce e st)))
  )
Proof
  rpt strip_tac >> irule every_state_insts_reason_message >>
  simp[outcomes_free_bytelike_literal] >>
  rpt strip_tac >> qpat_x_assum `!ce ty e st. _` irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem opcode_every_reason_message:
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
  !e ce st.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_expr_exists R e /\
  ~supported_expr_exists expr_shape_root e ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_reason_message ce e st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_reason_message >> simp[]
QED
