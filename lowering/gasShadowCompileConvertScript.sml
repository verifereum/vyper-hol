(* Value conversion compiler boundaries. *)
Theory gasShadowCompileConvert
Ancestors
  gasShadowCompileArith gasShadowCompileContext gasShadowCompileBase
  gasShadowState exprLowering compileEnv emitHelper venomInst

Theorem gas_shadow_compiles_load_bytestring_as_word:
  gas_shadow_compiles (load_bytestring_as_word v opc) (load_bytestring_as_word v opc)
Proof
  Cases_on `opc = SAR` >> simp[load_bytestring_as_word_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
                >- simp[] >> gen_tac >> BETA_TAC) >>
           simp[gas_shadow_compiles_return]) >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_int_clamp:
  gas_shadow_compiles (compile_int_clamp signed bits v) (compile_int_clamp signed bits v)
Proof
  Cases_on `signed` >> simp[compile_int_clamp_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_bytestring_widen_copy:
  gas_shadow_compiles (compile_bytestring_widen_copy dst_size v src_size)
    (compile_bytestring_widen_copy dst_size v src_size)
Proof
  simp[compile_bytestring_widen_copy_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_copy_memory]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_neg:
  gas_shadow_compiles (compile_neg v ty) (compile_neg v ty)
Proof
  Cases_on `type_bounds ty` >> simp[compile_neg_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_unwrap_value:
  gas_shadow_compiles (unwrap_value cenv vv) (unwrap_value cenv vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, gas_shadow_compiles_return] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >>
  simp[gas_shadow_compiles_ptr_load] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[LET_THM, gas_shadow_compiles_return, gas_shadow_compiles_ensure_in_memory]
QED

Theorem gas_shadow_compiles_materialize_vv:
  gas_shadow_compiles (compile_materialize_vv cenv ty vv)
    (compile_materialize_vv cenv ty vv)
Proof
  simp[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_unwrap_value,
               gas_shadow_compiles_store_memory]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_ifexp_arm:
  gas_shadow_compiles (compile_ifexp_arm cenv res_ty arm_ty vv)
    (compile_ifexp_arm cenv res_ty arm_ty vv)
Proof
  simp[compile_ifexp_arm_def, comp_ignore_bind_def] >>
  Cases_on `is_word_type res_ty \/ same_memory_layout cenv arm_ty res_ty` >>
  simp[gas_shadow_compiles_unwrap_value] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_unwrap_value,
               gas_shadow_compiles_store_memory]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_type_convert:
  gas_shadow_compiles (compile_type_convert v conv) (compile_type_convert v conv)
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, LET_THM, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> asm_rewrite_tac[] >>
  rpt (rpt IF_CASES_TAC >> asm_rewrite_tac[] >>
       pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_int_clamp, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_load_bytestring_as_word]
       >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  simp[gas_shadow_compiles_int_clamp, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return] >>
  pairarg_tac >> gvs[] >> rpt IF_CASES_TAC >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_int_clamp] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

(* mk_convert_op is pure; its execution uses the conversion boundary. *)
Theorem gas_shadow_compiles_mk_convert_op:
  gas_shadow_compiles (compile_type_convert v (mk_convert_op src_ty dst_ty))
    (compile_type_convert v (mk_convert_op src_ty dst_ty))
Proof
  simp[gas_shadow_compiles_type_convert]
QED
