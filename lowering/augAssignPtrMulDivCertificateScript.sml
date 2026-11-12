Theory augAssignPtrMulDivCertificate
Ancestors augAssignPtrScalarCertificate augAssignPtrScalarEmit
  augAssignPtrScalarClamp arithmeticProps exprLowering exprLoweringProps
  emitHelperProps compileEnv venomInst list rich_list pred_set

Theorem scalar_prefix_clamp:
  u.cs_current_insts = s.cs_current_insts ++ emitted_insts s u /\
  scalar_code A (emitted_insts s u) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u)))) r /\
  clamp_and_return r ty u = (op,t) ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >>
  drule_all scalar_clamp_and_return_code >> strip_tac >>
  drule clamp_and_return_extends >> strip_tac >>
  drule_all scalar_emitted_available_union >>
  disch_then (qspec_then `A` SUBST1_TAC) >>
  conj_tac
  >- (irule scalar_emitted_chain >> qexists `u` >> simp[]) >> simp[]
QED

Theorem compile_safe_mod_scalar_code:
  compile_safe_mod x y ty s = (op,t) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  gvs[compile_safe_mod_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
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

Theorem compile_safe_decimal_div_scalar_code:
  compile_safe_decimal_div x y divisor ty s = (op,t) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >>
  gvs[compile_safe_decimal_div_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `clamp_and_return res ty u = (op,t)` >>
  irule scalar_prefix_clamp >> qexistsl [`res`, `ty`, `u`] >>
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

Theorem compile_safe_div_scalar_code:
  compile_safe_div x y ty s = (op,t) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  Cases_on `type_bits ty = 256` >> Cases_on `type_bits ty < 256` >>
  gvs[compile_safe_div_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >> rpt (pairarg_tac >> gvs[])
  >~ [`clamp_and_return res ty u = (op,t)`]
  >- (irule scalar_prefix_clamp >> qexistsl [`res`, `ty`, `u`] >>
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
           GSYM UNION_ASSOC]) >>
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

Theorem compile_safe_div_mod_scalar_code:
  (compile_safe_div x y ty st = (op, st') \/
   compile_safe_mod x y ty st = (op, st') \/
   compile_safe_decimal_div x y divisor ty st = (op, st')) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts st st') /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) (emitted_insts st st')))) op
Proof
  metis_tac[compile_safe_div_scalar_code, compile_safe_mod_scalar_code,
            compile_safe_decimal_div_scalar_code]
QED

Theorem scalar_mul_checked_prefix:
  emit_op MUL [x;y] s = (res,u) /\
  compile_mul_overflow_check x y res signed bits u = ((),v) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts s v) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s v)))) res /\
  v.cs_current_insts = s.cs_current_insts ++ emitted_insts s v
Proof
  strip_tac >> drule scalar_emit_op_available >>
  disch_then (qspec_then `A` assume_tac) >>
  `scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u)))) x`
    by (irule scalar_available_after_code >> simp[]) >>
  `scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u)))) y`
    by (irule scalar_available_after_code >> simp[]) >>
  drule_all scalar_mul_overflow_check_code >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule compile_mul_overflow_check_extends >> strip_tac >>
  `scalar_code A (emitted_insts s u)` by
    (drule scalar_emit_op_code >> simp[scalar_binary_def]) >>
  conj_tac
  >- (irule scalar_emitted_chain >> qexists `u` >> simp[]) >>
  conj_tac
  >- (drule_all scalar_emitted_available_union >>
      disch_then (qspec_then `A` SUBST1_TAC) >>
      simp[scalar_available_union]) >>
  drule_all emitted_insts_append >> simp[]
QED

Theorem scalar_prefix_emit:
  u.cs_current_insts = s.cs_current_insts ++ emitted_insts s u /\
  scalar_code A (emitted_insts s u) /\ emit_op opc ops u = (r,t) /\
  EVERY (scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u))))) ops /\
  ((scalar_binary opc /\ LENGTH ops = 2) \/
   (scalar_unary opc /\ LENGTH ops = 1)) ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) r /\
  t.cs_current_insts = s.cs_current_insts ++ emitted_insts s t
Proof
  strip_tac >> drule scalar_emit_op_code >>
  disch_then (qspec_then
    `A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                (emitted_insts s u)))` mp_tac) >>
  simp[] >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  (conj_tac
  >- (irule scalar_emitted_chain >> qexists `u` >> simp[]) >>
  conj_tac
  >- (drule_all scalar_emitted_available_union >>
      disch_then (qspec_then `A` SUBST1_TAC) >>
      drule scalar_emit_op_available >> simp[]) >>
  drule_all emitted_insts_append >> simp[])
QED

Theorem scalar_mul_tail:
  u.cs_current_insts = s.cs_current_insts ++ emitted_insts s u /\
  scalar_code A (emitted_insts s u) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u)))) res /\
  (if decimal then emit_op (if signed then SDIV else Div) [res; Lit k] u
   else comp_return res u) = (res1,v) /\
  (if clamp then clamp_and_return res1 ty v
   else comp_return res1 v) = (op,t) ==>
  scalar_code A (emitted_insts s t) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) op
Proof
  strip_tac >> Cases_on `decimal` >> gvs[comp_return_def]
  >- (`scalar_code A (emitted_insts s v) /\
       scalar_available
         (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                      (emitted_insts s v)))) res1 /\
       v.cs_current_insts = s.cs_current_insts ++ emitted_insts s v`
      by (irule scalar_prefix_emit >>
          qexistsl [`if signed then SDIV else Div`, `[res; Lit k]`, `u`] >>
          simp[scalar_available_lit] >> Cases_on `signed` >>
          simp[scalar_binary_def]) >>
      Cases_on `clamp` >> gvs[comp_return_def] >>
      drule_all scalar_prefix_clamp >> simp[]) >>
  Cases_on `clamp` >> gvs[comp_return_def] >>
  drule_all scalar_prefix_clamp >> simp[]
QED

Theorem compile_safe_mul_scalar_code:
  compile_safe_mul x y ty st = (op, st') /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts st st') /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) (emitted_insts st st')))) op
Proof
  strip_tac >> Cases_on `type_bits ty > 128` >>
  gvs[compile_safe_mul_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule scalar_emit_op_code >>
  disch_then (qspec_then `A` mp_tac) >>
  simp[scalar_binary_def] >> strip_tac >>
  drule scalar_emit_op_available >>
  disch_then (qspec_then `A` assume_tac) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac scalar_mul_checked_prefix >>
  rpt (qpat_x_assum `!v u signed res bits. _` kall_tac) >>
  fs[COND_RATOR] >>
  metis_tac[scalar_mul_tail]
QED
