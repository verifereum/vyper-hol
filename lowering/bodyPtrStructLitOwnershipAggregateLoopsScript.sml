Theory bodyPtrStructLitOwnershipAggregateLoops
Ancestors bodyPtrStructLitOwnershipAggregateWrite bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipScratchFrame
  bodyPtrStructLitOwnershipSteps loweringShapeProps loweringShapeDefs
  loweringShapeRules context compileEnv exprLowering list unitShapeDefs stackPlanTypes

Theorem alloc_run_compile_make_tuple_frame:
  !es off R.
  shape_stable R /\
  (!e. MEM e es ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\vv s. value_shape_ok s vv) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\vv s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf)
    (compile_make_tuple cfn ce es buf off)
    (\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
      plain_operand s op)
Proof
  Induct
  >- simp[compile_make_tuple_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >>
  simp[compile_make_tuple_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\vv s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s buf /\ value_shape_ok s vv` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`F`, `ce`, `\s. R s /\ plain_operand s buf`] >>
      simp[shape_stable_conj, SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)] >>
      fs[MEM] >> metis_tac[]) >>
  gen_tac >> simp[] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
    (ABS_CONV (HO_REWR_CONV (GSYM comp_bind_assoc)))))) >>
  CONV_TAC (RATOR_CONV (RAND_CONV (HO_REWR_CONV (GSYM comp_bind_assoc)))) >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_aggregate_write_frame >> qexists `R` >> simp[]) >>
  gen_tac >> simp[] >> first_x_assum irule >> simp[] >> fs[MEM] >> metis_tac[]
QED

Theorem alloc_run_compile_make_array_elems_frame:
  !es idx R.
  shape_stable R /\
  (!e. MEM e es ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\vv s. value_shape_ok s vv) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\vv s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf)
    (compile_make_array_elems cfn ce es et elem_bytes lenword buf idx)
    (\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
      plain_operand s op)
Proof
  Induct
  >- simp[compile_make_array_elems_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >>
  simp[compile_make_array_elems_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\vv s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s buf /\ value_shape_ok s vv` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`F`, `ce`, `\s. R s /\ plain_operand s buf`] >>
      simp[shape_stable_conj, SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)] >>
      fs[MEM] >> metis_tac[]) >>
  gen_tac >> simp[] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
    (ABS_CONV (HO_REWR_CONV (GSYM comp_bind_assoc)))))) >>
  CONV_TAC (RATOR_CONV (RAND_CONV (HO_REWR_CONV (GSYM comp_bind_assoc)))) >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_aggregate_write_frame >> qexists `R` >> simp[]) >>
  gen_tac >> simp[] >> first_x_assum irule >> simp[] >> fs[MEM] >> metis_tac[]
QED

Theorem alloc_run_compile_make_array_frame:
  shape_stable R /\
  (!e. MEM e es ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\vv s. value_shape_ok s vv) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\vv s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf)
    (compile_make_array cfn ce es et elem_bytes lenword buf)
    (\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
      plain_operand s op)
Proof
  strip_tac >>
  simp[compile_make_array_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf` >>
  reverse conj_tac
  >- (Cases_on `lenword`
      >- (simp[] >> irule alloc_run_conseq >> irule_at Any alloc_run_mstore_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, plain_operand_def, is_label_operand_def,
        SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> irule alloc_run_compile_make_array_elems_frame >> simp[]
QED
