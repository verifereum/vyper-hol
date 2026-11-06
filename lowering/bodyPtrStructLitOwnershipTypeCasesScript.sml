Theory bodyPtrStructLitOwnershipTypeCases
Ancestors bodyPtrStructLitOwnershipConvert bodyPtrStructLitOwnershipBytesPrefix
  bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering context compileEnv
  builtinSimple exprCallBounds compilerFirstEmission list pair

Theorem compile_builtin_empty_complex_alloc_run:
  !nbytes bs st v st'.
  compile_builtin_empty_complex nbytes bs st = (v,st') ==>
  fresh_outputs st ==> alloc_writers_unique st ==>
  alloc_writers_unique st' /\ alloc_frame st st' /\ fresh_outputs st'
Proof
  rpt gen_tac >>
  mp_tac alloc_run_compile_builtin_empty_complex >>
  simp[alloc_run_def] >> metis_tac[]
QED

Theorem alloc_run_type_builtin_constants:
  tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args) (\v s. T)
Proof
  strip_tac >> gvs[] >>
  simp[alloc_run_def, compile_type_builtin_dispatch_body_def] >>
  rpt gen_tac >> rpt strip_tac >> gvs[AllCaseEqs(), alloc_frame_refl] >>
  pairarg_tac >> gvs[alloc_frame_refl] >>
  `fresh_outputs s` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  drule compile_builtin_empty_complex_alloc_run >> simp[]
QED

Theorem compile_type_convert_alloc_run:
  !v conv st out st'. compile_type_convert v conv st = (out,st') ==>
  fresh_outputs st ==> alloc_writers_unique st ==>
  alloc_writers_unique st' /\ alloc_frame st st' /\ fresh_outputs st'
Proof
  rpt gen_tac >> mp_tac (Q.SPEC `conv` alloc_run_compile_type_convert) >>
  simp[alloc_run_def] >> metis_tac[]
QED

Theorem compile_bytestring_widen_copy_alloc_run:
  !dst v src st out st'. compile_bytestring_widen_copy dst v src st = (out,st') ==>
  fresh_outputs st ==> alloc_writers_unique st ==>
  alloc_writers_unique st' /\ alloc_frame st st' /\ fresh_outputs st'
Proof
  rpt gen_tac >> mp_tac alloc_run_compile_bytestring_widen_copy >>
  simp[alloc_run_def] >> metis_tac[]
QED

Theorem alloc_run_type_builtin_convert:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce (expr_type (HD args)) (HD args)) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce (expr_type (HD args)) (HD args)) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty Convert rt args) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  Cases_on `rt` >> simp[] >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs(), alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >> gvs[alloc_frame_refl] >>
  `fresh_outputs st1` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  FIRST [drule compile_type_convert_alloc_run,
    drule compile_bytestring_widen_copy_alloc_run] >> simp[]
QED


Theorem alloc_run_type_builtin_extract32:
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) /\
  2 <= LENGTH args ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty Extract32 rt args) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[]) >>
  gen_tac >> simp[Once state_pair_let_bind, SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_bytestring_src_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `lds` >> PairCases_on `lds` >> simp[] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> simp[MEM_EL] >> qexists `1` >> simp[]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  qexistsl [`fresh_outputs`, `\v s. fresh_outputs s`] >>
  simp[shape_state_def, shape_base_fresh_outputs] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_compile_extract32_load] >>
  gen_tac >> simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  mp_tac (Q.INST [`val_op` |-> `v`, `ty` |-> `rt`]
    alloc_run_compile_clamp_basetype) >> simp[alloc_run_def] >>
  disch_then drule >> simp[]
QED

Theorem alloc_run_type_builtin_nonabi:
  (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon \/
   tb = Convert \/ tb = Extract32) /\
  type_builtin_arity tb <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args) (\v s. T)
Proof
  strip_tac >> gvs[]
  >- (irule alloc_run_type_builtin_constants >> simp[])
  >- (irule alloc_run_type_builtin_constants >> simp[])
  >- (irule alloc_run_type_builtin_constants >> simp[])
  >- (irule alloc_run_type_builtin_constants >> simp[])
  >- (irule alloc_run_type_builtin_convert >>
      `MEM (HD args) args` by (Cases_on `args` >> gvs[type_builtin_arity_def]) >>
      first_x_assum (qspecl_then [`HD args`, `expr_type (HD args)`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  irule alloc_run_type_builtin_extract32 >> simp[] >>
  gvs[type_builtin_arity_def] >> qexists `internal` >> simp[]
QED
