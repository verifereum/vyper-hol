Theory bodyPtrStructLitTargetArray
Ancestors bodyPtrStructLitTargetScalar bodyPtrStructLitOwnershipSubscriptTails
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering
  stackPlanTypes venomInst context compileEnv unitShapeDefs list

Theorem array_plain_stable[local]:
  shape_stable (\s. plain_operand s op)
Proof
  mp_tac (Q.SPEC `[op]` shape_stable_plain_operands) >> simp[]
QED

Theorem array_literal_plain[local,simp]:
  plain_operand s (Lit w)
Proof
  simp[plain_operand_def, is_label_operand_def]
QED

Theorem array_assert_shape[local]:
  shape_stable R /\ (!s. R s ==> plain_operand s valid_op) ==>
  shape_step internal compiler_label R (emit_void ASSERT [valid_op]) (\u s. R s)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any shape_step_emit_void_pre >>
  qexistsl [`R`, `\s. plain_operand s valid_op`, `compiler_label`] >>
  simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, EVERY_MEM, plain_operand_def]
QED

Theorem array_address_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\s. R s /\ plain_operand s base_op /\ plain_operand s idx_op)
    (do data_ptr <- (if dyn then emit_op ADD [base_op;Lit (n2w scale_n)]
                     else return base_op);
        offset <- emit_op MUL [idx_op;Lit (n2w bytes_n)];
        emit_op ADD [data_ptr;offset] od)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\p s. (R s /\ plain_operand s idx_op) /\ plain_operand s p` >>
  reverse conj_tac
  >- (Cases_on `dyn` >> simp[]
      >- (irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
          qexists `\s. R s /\ plain_operand s idx_op` >>
          simp[shape_stable_conj, array_plain_stable]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >> irule target_scalar_op_bind >>
  simp[shape_stable_conj, array_plain_stable] >> gen_tac >>
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `R` >> simp[]
QED

Theorem array_bounds_address_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\s. R s /\ plain_operand s len_op /\ plain_operand s base_op /\ plain_operand s idx_op)
    (do neg <- (if signed_idx then emit_op SLT [idx_op;Lit 0w] else return (Lit 0w));
        oob <- emit_op LT [idx_op;len_op];
        not_oob <- emit_op ISZERO [oob];
        invalid <- emit_op OR [neg;not_oob];
        valid <- emit_op ISZERO [invalid];
        emit_void ASSERT [valid];
        data_ptr <- (if dyn then emit_op ADD [base_op;Lit (n2w scale_n)] else return base_op);
        offset <- emit_op MUL [idx_op;Lit (n2w bytes_n)];
        emit_op ADD [data_ptr;offset] od)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule shape_step_bind >>
  qexists `\v s. (R s /\ plain_operand s len_op /\ plain_operand s base_op /\
    plain_operand s idx_op) /\ plain_operand s v` >> reverse conj_tac
  >- (Cases_on `signed_idx` >> simp[]
      >- (irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
          qexists `\s. R s /\ plain_operand s len_op /\ plain_operand s base_op /\
            plain_operand s idx_op` >> simp[shape_stable_conj, array_plain_stable]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >>
  ntac 4 (irule target_scalar_op_bind >> simp[shape_stable_conj, array_plain_stable] >>
    TRY (reverse conj_tac >-
      (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >> simp[array_plain_stable])) >>
    gen_tac) >>
  rename1 `emit_void ASSERT [valid_op]` >>
  irule shape_step_bind >>
  qexists `\u s. R s /\ plain_operand s base_op /\ plain_operand s idx_op` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any array_assert_shape >>
      qexists `\s. R s /\ plain_operand s base_op /\ plain_operand s idx_op /\
        plain_operand s valid_op` >> simp[shape_stable_conj, array_plain_stable]) >>
  gen_tac >> simp[] >> irule array_address_shape >> simp[]
QED

Theorem target_array_shape[local]:
  shape_stable R /\
  (!op. shape_step internal compiler_label (\s. R s /\ plain_operand s op)
    (loader op) (\v s. R s /\ plain_operand s v)) ==>
  shape_step internal compiler_label
    (\s. R s /\ plain_operand s base_op /\ plain_operand s idx_op)
    (compile_array_subscript base_op idx_op dyn count_n scale_n bytes_n signed_idx loader)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> simp[compile_array_subscript_def] >>
  irule shape_step_bind >>
  qexists `\v s. R s /\ plain_operand s v /\ plain_operand s base_op /\ plain_operand s idx_op` >>
  conj_tac
  >- (gen_tac >> simp[] >> irule array_bounds_address_shape >> simp[]) >>
  Cases_on `dyn` >> simp[]
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      first_assum (irule_at Any) >>
      qexists `\s. plain_operand s base_op /\ plain_operand s idx_op` >>
      simp[shape_stable_conj, array_plain_stable]) >>
  irule shape_step_return >> simp[]
QED

Theorem target_array_certificate:
  shape_stable R /\
  (!op. shape_step internal compiler_label (\s. R s /\ plain_operand s op)
    (loader op) (\v s. R s /\ plain_operand s v)) /\
  (!op. alloc_run fresh_outputs (loader op) (\v s. fresh_outputs s)) ==>
  shape_step internal compiler_label
    (\s. R s /\ plain_operand s base_op /\ plain_operand s idx_op)
    (compile_array_subscript base_op idx_op dyn count_n scale_n bytes_n signed_idx loader)
    (\v s. R s /\ plain_operand s v) /\
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s base_op /\ plain_operand s idx_op)
    (compile_array_subscript base_op idx_op dyn count_n scale_n bytes_n signed_idx loader)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> conj_tac >- (irule target_array_shape >> simp[]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
  irule_at Any target_array_shape >>
  irule_at Any alloc_run_compile_array_subscript >>
  qexistsl [`internal`, `\s. T`, `R`] >> simp[shape_stable_def]
QED
