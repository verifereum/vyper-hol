Theory bodyPtrStructLitCreationFrames
Ancestors bodyPtrStructLitCreationShape bodyPtrStructLitEmitterFrame
  bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitCreationCopyFrames
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipCallSuffix
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps
  exprLowering builtinCreate compileEnv context list

Theorem alloc_run_create_blueprint_check_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s target /\ plain_operand s offset)
    (compile_create_blueprint_check target offset)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_create_blueprint_check, create_blueprint_check_shape]
QED

Theorem alloc_run_create_proxy_buf_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s target)
    (compile_create_proxy_buf target)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\buf s. shape_state s /\ (R s /\ plain_operand s target) /\
    plain_operand s buf.buf_operand` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_alloc_buffer_frame >>
      qexists `\s. R s /\ plain_operand s target` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[target]` shape_stable_plain_operands)]) >>
  qx_gen_tac `buf` >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[Once comp_bind_def, comp_return_def] >> simp[SF ETA_ss] >>
  rpt (FIRST [ho_match_mp_tac alloc_run_op_bind,
      ho_match_mp_tac alloc_run_void_bind] >>
    simp[SRULE [stackPlanTypesTheory.is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
    (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
    (conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def])) >> rpt gen_tac) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_create_salt_frame:
  shape_stable R /\
  (!e. salt_e = SOME e ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_create_salt cfn ce salt_e)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      (case v of NONE => T | SOME op => plain_operand s op))
Proof
  strip_tac >> Cases_on `salt_e`
  >- simp[compile_create_salt_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  gvs[] >> simp[compile_create_salt_def] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_lower_value_frame) >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_create_snapshot_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s (vv_operand vv))
    (compile_create_snapshot ce vv ty)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v)
Proof
  strip_tac >> simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\b s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s (vv_operand vv)) /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (ho_match_mp_tac alloc_run_alloc_buffer_frame >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[vv_operand vv]` shape_stable_plain_operands)]) >>
  qx_gen_tac `b` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- suspend "copy" >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_snapshot_frame[copy]:
  Cases_on `vv_location vv` >>
  TRY (rename1 `_ = SOME loc` >> Cases_on `loc`) >> simp[] >>
  TRY (rename1 `compile_copy_memory_dynamic _ _ _` >>
    irule alloc_run_conseq >> irule_at Any alloc_run_create_bytes_copy_frame >>
    qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s b.buf_operand` >>
    simp[shape_stable_conj, cenv_shape_ok_stable,
      SRULE [] (Q.SPEC `[b.buf_operand]` shape_stable_plain_operands)] >> NO_TAC) >>
  (irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (irule alloc_run_conseq >>
      FIRST [irule_at Any alloc_run_create_slot_copy_frame,
        irule_at Any alloc_run_create_code_copy_frame] >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s b.buf_operand` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[b.buf_operand]` shape_stable_plain_operands)]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

Finalise alloc_run_create_snapshot_frame
