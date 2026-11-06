Theory augAssignPtrScalarClamp
Ancestors augAssignPtrScalarEmit augAssignPtrScalarCertificate
          arithmeticProps exprLowering exprLoweringProps emitHelperProps
          venomInst pred_set list compileEnv

Theorem scalar_compile_clamp_code:
  compile_clamp x ty s = ((),t) /\ scalar_available A x ==>
  scalar_code A (emitted_insts s t)
Proof
  strip_tac >>
  gvs[compile_clamp_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac scalar_emit_op_available >>
  rpt (qpat_x_assum `!A. scalar_available _ _`
    (qspec_then `{}` assume_tac)) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  imp_res_tac (cj 1 emitted_insts_emit_void) >>
  imp_res_tac (cj 2 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, scalar_available_union, scalar_available_lit,
       GSYM UNION_ASSOC]
QED

Theorem scalar_clamp_and_return_code:
  clamp_and_return x ty s = (r,t) /\ scalar_available A x ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) r
Proof
  simp[clamp_and_return_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[]
  >- (drule_all scalar_compile_clamp_code >> simp[]) >>
  irule scalar_available_after_code >> simp[]
QED

Theorem scalar_mul_overflow_check_code:
  compile_mul_overflow_check x y res signed bits s = ((),t) /\
  scalar_available A x /\ scalar_available A y /\ scalar_available A res ==>
  scalar_code A (emitted_insts s t)
Proof
  strip_tac >>
  Cases_on `signed` >> Cases_on `bits = 256` >>
  gvs[compile_mul_overflow_check_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac scalar_emit_op_available >>
  rpt (qpat_x_assum `!A. scalar_available _ _`
    (qspec_then `{}` assume_tac)) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  imp_res_tac (cj 1 emitted_insts_emit_void) >>
  imp_res_tac (cj 2 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, scalar_available_union, scalar_available_lit,
       GSYM UNION_ASSOC]
QED
