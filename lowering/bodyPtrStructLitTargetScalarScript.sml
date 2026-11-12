Theory bodyPtrStructLitTargetScalar
Ancestors bodyPtrStructLitOwnershipSubscriptTails bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipFreshness
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering
  stackPlanTypes venomInst context compileEnv unitShapeDefs list

Theorem target_scalar_op_shape:
  shape_stable R /\ MEM opc [ADD; MLOAD; SHA3; SLT; LT; ISZERO; OR; MUL] ==>
  shape_step internal compiler_label
    (\s. R s /\ EVERY (plain_operand s) ops) (emit_op opc ops)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
  qexistsl [`R`, `\s. EVERY (plain_operand s) ops`, `compiler_label`] >>
  gvs[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, EVERY_MEM, plain_operand_def] >>
  rpt strip_tac >> rpt (CASE_TAC >> gvs[EVERY_MEM, is_label_operand_def]) >>
  metis_tac[is_label_operand_def]
QED

Theorem target_scalar_store_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\s. R s /\ EVERY (plain_operand s) ops) (emit_void MSTORE ops)
    (\v s. R s)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any shape_step_emit_void_pre >>
  qexistsl [`R`, `\s. EVERY (plain_operand s) ops`, `compiler_label`] >>
  gvs[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, EVERY_MEM, plain_operand_def] >>
  rpt strip_tac >> rpt (CASE_TAC >> gvs[EVERY_MEM, is_label_operand_def]) >>
  metis_tac[is_label_operand_def]
QED

Theorem target_scalar_op_bind:
  shape_stable R /\ MEM opc [ADD; MLOAD; SHA3; SLT; LT; ISZERO; OR; MUL] /\
  (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!v. shape_step internal compiler_label (\s. R s /\ plain_operand s v) (k v) Q) ==>
  shape_step internal compiler_label R (comp_bind (emit_op opc ops) k) Q
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. R s /\ plain_operand s v` >> simp[] >>
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `R` >> simp[]
QED

Theorem target_scalar_store_bind[local]:
  shape_stable R /\ (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!u. shape_step internal compiler_label R (k u) Q) ==>
  shape_step internal compiler_label R (comp_bind (emit_void MSTORE ops) k) Q
Proof
  strip_tac >> irule shape_step_bind >> qexists `\u s. R s` >> simp[SF ETA_ss] >>
  irule shape_step_conseq >> irule_at Any target_scalar_store_shape >>
  qexists `R` >> simp[]
QED

Theorem target_scalar_alloc_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_alloc_buffer n)
    (\b s. R s /\ plain_operand s b.buf_operand)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any compile_alloc_buffer_shape >>
  qexists `R` >> simp[]
QED

Theorem target_literal_plain[local,simp]:
  plain_operand s (Lit w)
Proof
  simp[plain_operand_def, is_label_operand_def]
QED

Theorem target_mapping_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\s. R s /\ EVERY (plain_operand s) [base_op; key_op])
    (compile_mapping_subscript base_op key_op)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> simp[compile_mapping_subscript_def, comp_ignore_bind_def] >>
  irule shape_step_bind >>
  qexists `\b s. (R s /\ EVERY (plain_operand s) [base_op;key_op]) /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (simp[EVERY_DEF] >> ho_match_mp_tac target_scalar_alloc_shape >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >> irule target_scalar_store_bind >>
  simp[shape_stable_conj, shape_stable_plain_operands, SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)] >>
  irule target_scalar_op_bind >>
  simp[shape_stable_conj, shape_stable_plain_operands, SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands),
    target_literal_plain] >> gen_tac >>
  irule target_scalar_store_bind >>
  simp[shape_stable_conj, shape_stable_plain_operands, SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands),
    target_literal_plain] >>
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `R` >> simp[plain_operand_def, is_label_operand_def]
QED

Theorem target_key_hash_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\s. R s /\ plain_operand s key_op)
    (compile_keccak256_key key_op bytes32_key) (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> simp[compile_keccak256_key_def, comp_ignore_bind_def] >>
  Cases_on `bytes32_key` >> simp[]
  >- (irule shape_step_bind >>
      qexists `\b s. (R s /\ plain_operand s key_op) /\ plain_operand s b.buf_operand` >>
      reverse conj_tac
      >- (ho_match_mp_tac target_scalar_alloc_shape >>
          simp[shape_stable_conj,
            SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)]) >>
      gen_tac >> simp[] >> irule target_scalar_store_bind >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)] >>
      irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
      qexists `R` >> simp[]) >>
  irule target_scalar_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)] >> gen_tac >>
  irule target_scalar_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)] >> gen_tac >>
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `R` >> simp[]
QED

Theorem target_mapping_certificate:
  shape_stable R ==>
  shape_step internal compiler_label
    (\s. R s /\ EVERY (plain_operand s) [base_op; key_op])
    (compile_mapping_subscript base_op key_op) (\v s. R s /\ plain_operand s v) /\
  alloc_run (\s. shape_state s /\ R s /\ EVERY (plain_operand s) [base_op;key_op])
    (compile_mapping_subscript base_op key_op)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> conj_tac >- simp[target_mapping_shape] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
  irule_at Any target_mapping_shape >>
  irule_at Any alloc_run_compile_mapping_subscript >>
  qexistsl [`\s. T`, `R`] >> simp[shape_stable_def]
QED

Theorem target_key_hash_certificate:
  shape_stable R ==>
  shape_step internal compiler_label (\s. R s /\ plain_operand s key_op)
    (compile_keccak256_key key_op bytes32_key) (\v s. R s /\ plain_operand s v) /\
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s key_op)
    (compile_keccak256_key key_op bytes32_key)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> conj_tac >- simp[target_key_hash_shape] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
  irule_at Any target_key_hash_shape >>
  irule_at Any alloc_run_compile_keccak256_key >>
  qexistsl [`\s. T`, `R`] >> simp[shape_stable_def]
QED
