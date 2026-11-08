Theory bodyPtrStructLitOwnershipConcatCases
Ancestors bodyPtrStructLitOwnershipConcatFrame bodyPtrStructLitOwnershipIfexpFrame
  bodyPtrStructLitOwnershipSteps loweringShapeProps loweringShapeDefs loweringShapeRules
  exprLowering compileEnv context list gasShadowCompileBase stackPlanTypes unitShapeDefs

Theorem concat_alloc_bind[local]:
  shape_stable R /\
  (!b. alloc_run (\s. shape_state s /\ R s /\ plain_operand s b.buf_operand) (k b) Q) ==>
  alloc_run (\s. shape_state s /\ R s) (comp_bind (compile_alloc_buffer n) k) Q
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ R s /\ plain_operand s b.buf_operand` >>
  simp[alloc_run_alloc_buffer_frame]
QED

Theorem alloc_run_builtin_concat:
  (!e. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Concat max_len) args) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  ho_match_mp_tac concat_alloc_bind >> simp[cenv_shape_ok_stable] >>
  qx_gen_tac `buf` >> simp[] >>
  ho_match_mp_tac alloc_run_concat_op_bind >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
    SRULE [is_label_operand_def] (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
  qx_gen_tac `data_ptr` >>
  ho_match_mp_tac concat_alloc_bind >>
  (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
    simp[cenv_shape_ok_stable, SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
  qx_gen_tac `off` >> simp[] >>
  ho_match_mp_tac alloc_run_concat_void_bind >>
  simp[SRULE [is_label_operand_def] (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
  (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
    simp[cenv_shape_ok_stable, SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand /\
    EVERY (plain_operand s) [data_ptr;off.buf_operand]` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_concat_frame >>
      qexists `\s. plain_operand s buf.buf_operand` >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  simp[] >> ho_match_mp_tac alloc_run_concat_op_bind >> simp[] >>
  (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
    simp[cenv_shape_ok_stable, SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
  gen_tac >> ho_match_mp_tac alloc_run_concat_void_bind >> simp[] >>
  (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
    simp[cenv_shape_ok_stable, SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
