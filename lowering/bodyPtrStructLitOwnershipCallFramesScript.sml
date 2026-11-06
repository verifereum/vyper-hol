Theory bodyPtrStructLitOwnershipCallFrames
Ancestors bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFrame
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering context compileEnv list

Theorem alloc_run_compile_multi_vvs_frame:
  !es R.
  shape_stable R /\
  (!e. MEM e es ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_multi_vvs cfn ce es)
    (\vs s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ EVERY (value_shape_ok s) vs)
Proof
  Induct
  >- simp[compile_multi_vvs_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >> simp[compile_multi_vvs_def] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_struct_child_frame) >> simp[]) >>
  qx_gen_tac `vv` >> simp[] >> irule alloc_run_bind >>
  qexists `\vs s. shape_state s /\ (R s /\ value_shape_ok s vv) /\
    cenv_shape_ok s ce /\ EVERY (value_shape_ok s) vs` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      qpat_assum `!R. _` (irule_at Any) >>
      qexists `\s. R s /\ value_shape_ok s vv` >>
      simp[shape_stable_conj, value_shape_ok_stable] >> metis_tac[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_materialize_vv_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s vv)
    (compile_materialize_vv ce ty vv)
    (\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s op)
Proof
  strip_tac >> simp[compile_materialize_vv_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\b s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ value_shape_ok s vv) /\ plain_operand s b.buf_operand` >>
  reverse conj_tac
  >- (ho_match_mp_tac alloc_run_alloc_buffer_frame >>
      simp[shape_stable_conj, cenv_shape_ok_stable, value_shape_ok_stable]) >>
  qx_gen_tac `buf` >> simp[] >> irule alloc_run_bind >>
  qexists `\src s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand) /\ plain_operand s src` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. R s /\ plain_operand s buf.buf_operand`]
        alloc_run_unwrap_value_frame) >>
      qexistsl [`buf`, `\s. R s /\ cenv_shape_ok s ce`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands)]) >>
  qx_gen_tac `src` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand) /\ T` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand`]
        alloc_run_store_memory_frame) >> qexistsl [`buf`, `R`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands)]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_ext_call_kwarg_frame:
  shape_stable R /\
  (!ty. shape_step F compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_ext_call_kwarg cfn ce rt k e)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s (FST v))
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (irule alloc_run_bind >>
      qexists `\vv s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s vv` >>
      reverse conj_tac
      >- (irule (Q.INST [`internal` |-> `F`] alloc_run_struct_child_frame) >> simp[]) >>
      qx_gen_tac `vv` >> simp[] >> irule alloc_run_bind >>
      qexists `\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s op` >>
      reverse conj_tac >- (irule alloc_run_compile_materialize_vv_frame >> simp[]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  irule alloc_run_bind >>
  qexists `\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s op` >>
  reverse conj_tac
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_lower_value_frame) >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_ext_call_kwargs_frame:
  !ks es R. shape_stable R /\
  (!e ty. MEM e es ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce ty e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_ext_call_kwargs cfn ce rt ks es)
    (\vs s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      EVERY (plain_operand s)
        ((case FST vs of NONE => [] | SOME v => [v]) ++
         (case FST (SND vs) of NONE => [] | SOME v => [v]) ++
         (case SND (SND vs) of NONE => [] | SOME v => [FST v])))
Proof
  Induct
  >- simp[compile_ext_call_kwargs_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >> Cases_on `es`
  >- simp[compile_ext_call_kwargs_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[compile_ext_call_kwargs_def] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s (FST v)` >>
  reverse conj_tac
  >- (irule alloc_run_compile_ext_call_kwarg_frame >> simp[]) >>
  qx_gen_tac `opty` >> PairCases_on `opty` >> simp[] >> irule alloc_run_bind >>
  qexists `\vs s. shape_state s /\ (R s /\ plain_operand s opty0) /\ cenv_shape_ok s ce /\
    EVERY (plain_operand s)
      ((case FST vs of NONE => [] | SOME v => [v]) ++
       (case FST (SND vs) of NONE => [] | SOME v => [v]) ++
       (case SND (SND vs) of NONE => [] | SOME v => [FST v]))` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> qpat_assum `!es R. _` (irule_at Any) >>
      qexists `\s. R s /\ plain_operand s opty0` >>
      simp[shape_stable_conj, SRULE [] (Q.SPEC `[opty0]` shape_stable_plain_operands)] >>
      metis_tac[]) >>
  qx_gen_tac `opts` >> PairCases_on `opts` >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt strip_tac >> rpt (IF_CASES_TAC >> simp[])
QED
