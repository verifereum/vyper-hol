Theory augAssignPtrRemainingCertificate
Ancestors augAssignPtrMulDivCertificate augAssignPtrCheckedCertificate
  augAssignPtrScalarCertificate augAssignPtrScalarEmit augAssignPtrScalarClamp
  arithmeticProps exprLowering exprLoweringProps builtinSimple
  emitHelperProps compileEnv venomInst list rich_list pred_set

Theorem wrap_truncate_scalar_code:
  wrap_truncate r ty s = (op,t) /\ scalar_available A r ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >>
  Cases_on `is_signed_type ty` >>
  gvs[wrap_truncate_def, comp_return_def]
  >> imp_res_tac scalar_emit_op_available >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  gvs[scalar_code_singleton, scalar_shape_def, mk_inst_def,
      scalar_binary_def, scalar_available_lit,
      emitted_insts_def, scalar_code_def]
QED

Theorem compile_select_scalar_code:
  compile_select c x y s = (op,t) /\
  scalar_available A c /\ scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >>
  gvs[compile_select_def, comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac scalar_emit_op_available >>
  rpt (qpat_x_assum `!A. scalar_available _ _`
    (qspec_then `{}` assume_tac)) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  imp_res_tac (cj 2 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, scalar_available_union, scalar_available_lit,
       GSYM UNION_ASSOC]
QED

Theorem compile_compare_scalar_code:
  compile_compare bop x y ty s = (op,t) /\
  MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> Cases_on `bop` >> gvs[] >> Cases_on `is_uint256 ty` >>
  gvs[compile_compare_def, comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac scalar_emit_op_available >>
  rpt (qpat_x_assum `!A. scalar_available _ _`
    (qspec_then `{}` assume_tac)) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  imp_res_tac (cj 2 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, scalar_available_union, scalar_available_lit,
       GSYM UNION_ASSOC]
QED

Theorem compile_safe_pow_fallback_scalar_code:
  compile_safe_pow x y ty NONE NONE s = (op,t) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  simp[compile_safe_pow_def, GSYM clamp_and_return_def,
       comp_bind_def] >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  irule scalar_prefix_clamp >> goal_assum (drule_at Any) >>
  drule emit_op_extends >> strip_tac >>
  drule scalar_emit_op_available >>
  disch_then (qspec_then `A` assume_tac) >>
  simp[] >> irule scalar_emit_op_code >> goal_assum (drule_at Any) >>
  simp[scalar_binary_def]
QED

Theorem compile_safe_pow_scalar_code:
  compile_safe_pow x y ty bl el s = (op,t) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  Cases_on `bl` >> Cases_on `el`
  >- metis_tac[compile_safe_pow_fallback_scalar_code] >>
  strip_tac >> Cases_on `is_signed_type ty` >>
  gvs[compile_safe_pow_def] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _`
    (fn th => mp_tac th)) >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac scalar_emit_op_available >>
  rpt (qpat_x_assum `!A. scalar_available _ _`
    (qspec_then `{}` assume_tac)) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  imp_res_tac (cj 1 emitted_insts_emit_void) >>
  imp_res_tac (cj 2 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, scalar_available_union, scalar_available_lit,
       GSYM UNION_ASSOC]
QED

Theorem scalar_emitted_result_chain:
  u.cs_current_insts = s.cs_current_insts ++ emitted_insts s u /\
  t.cs_current_insts = u.cs_current_insts ++ emitted_insts u t /\
  scalar_code A (emitted_insts s u) /\
  scalar_code
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u))))
    (emitted_insts u t) /\
  scalar_available
    ((A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                  (emitted_insts s u)))) UNION
     BIGUNION (set (MAP (\i. set i.inst_outputs) (emitted_insts u t)))) op ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> conj_tac
  >- (irule scalar_emitted_chain >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all scalar_emitted_available_union >>
  disch_then (qspec_then `A` SUBST1_TAC) >> simp[]
QED

Theorem wrap_truncate_extends_scalar:
  wrap_truncate r ty s = (op,t) ==>
  t.cs_current_insts = s.cs_current_insts ++ emitted_insts s t
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, comp_return_def] >> strip_tac >> gvs[]
  >- (drule emit_op_extends >> simp[]) 
  >- (drule emit_op_extends >> simp[]) >>
  simp[emitted_insts_def]
QED

Theorem scalar_emit_wrap_code:
  emit_op opc [x;y] s = (r,u) /\ wrap_truncate r ty u = (op,t) /\
  scalar_binary opc /\ scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> drule scalar_emit_op_available >>
  disch_then (qspec_then `A` assume_tac) >>
  drule_all wrap_truncate_scalar_code >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule wrap_truncate_extends_scalar >> strip_tac >>
  irule scalar_emitted_result_chain >> goal_assum (drule_at Any) >> simp[] >>
  irule scalar_emit_op_code >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_select_extends_scalar:
  compile_select c x y s = (op,t) ==>
  t.cs_current_insts = s.cs_current_insts ++ emitted_insts s t
Proof
  simp[compile_select_def, comp_bind_def] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac emit_op_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem scalar_emit_select_code:
  emit_op opc [x;y] s = (r,u) /\ compile_select r x y u = (op,t) /\
  scalar_binary opc /\ scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> drule scalar_emit_op_available >>
  disch_then (qspec_then `A` assume_tac) >>
  `scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u)))) x /\
   scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u)))) y`
    by simp[scalar_available_union] >>
  drule_all compile_select_scalar_code >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule compile_select_extends_scalar >> strip_tac >>
  irule scalar_emitted_result_chain >> goal_assum (drule_at Any) >> simp[] >>
  irule scalar_emit_op_code >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_binop_scalar_code:
  compile_binop bop x y ty bl el s = (op,t) /\
  MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
           UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt;
           GtE; Exp; Min; Max; In; NotIn] /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> Cases_on `bop` >> gvs[] >>
  gvs[compile_binop_def]
  >~ [`compile_safe_add x y ty s = (op,t)`]
  >- metis_tac[compile_safe_add_sub_scalar_code]
  >~ [`compile_safe_sub x y ty s = (op,t)`]
  >- metis_tac[compile_safe_add_sub_scalar_code]
  >~ [`compile_safe_mul x y ty s = (op,t)`]
  >- (drule_all compile_safe_mul_scalar_code >> simp[])
  >~ [`compile_safe_mod x y ty s = (op,t)`]
  >- (drule_all compile_safe_mod_scalar_code >> simp[])
  >~ [`(if is_decimal_type ty then _ else _) s = (op,t)`]
  >- (Cases_on `is_decimal_type ty` >> gvs[] >>
      metis_tac[compile_safe_div_mod_scalar_code])
  >>~- ([`compile_compare _ _ _ _ _ = _`],
    drule compile_compare_scalar_code >> simp[])
  >>~- ([`compile_safe_pow _ _ _ _ _ _ = _`],
    drule_all compile_safe_pow_scalar_code >> simp[]) >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  all_tac
  >>~- ([`wrap_truncate _ _ _ = _`],
    drule scalar_emit_wrap_code >> simp[scalar_binary_def] >>
    disch_then drule_all >> simp[])
  >>~- ([`compile_select _ _ _ _ = _`],
    drule scalar_emit_select_code >> simp[scalar_binary_def] >>
    disch_then drule_all >> simp[]) >>
  imp_res_tac scalar_emit_op_available >>
  rpt (qpat_x_assum `!A. scalar_available _ _`
    (qspec_then `{}` assume_tac)) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac (cj 1 emitted_insts_emit_op_local) >>
  imp_res_tac (cj 2 emitted_insts_emit_op_local) >>
  gvs[mk_inst_def] >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, scalar_available_union, scalar_available_lit,
       GSYM UNION_ASSOC]
QED
