(* Expression compilation preserves reserved-operand exclusion. *)
Theory runtimeLabelExpr
Ancestors
  runtimeLabelBuiltins runtimeLabelABI runtimeLabelInvariant runtimeLabelValues
  exprLowering exprCallBounds

Theorem rb_as_ptr_val:
  rb_step rb_operand_ok m ==>
  rb_step rb_value_ok (\st. as_ptr_val ty loc (m st))
Proof
  simp[rb_step_def] >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> Cases_on `m st` >>
  simp[as_ptr_val_def, rb_value_ok_def, rb_mk_ptr]
QED

Theorem rb_compile_type_builtin_dispatch_body:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) ==>
  rb_step rb_value_ok
    (compile_type_builtin_dispatch_body cfn ce vv_ty ty tb ret_ty args)
Proof
  strip_tac >> Cases_on `tb` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_type_builtin_dispatch_body_def, LET_THM] >>
  BETA_TAC >> simp_tac (srw_ss()) []
  >~ [`lower_value cfn ce (expr_type (HD args))`] >- suspend "convert"
  >~ [`compile_builtin_empty_complex`] >- suspend "empty"
  >~ [`type_bounds ret_ty`] >- suspend "bounds"
  >~ [`type_bounds ret_ty`] >- suspend "bounds2"
  >~ [`StackValue vv_ty (Lit 1w)`] >- suspend "epsilon"
  >~ [`compile_extract32_load`] >- suspend "extract"
  >~ [`lower_abi_encode`] >- suspend "encode"
  >> suspend "decode"
QED

Resume rb_compile_type_builtin_dispatch_body[bounds]:
  Cases_on `type_bounds ret_ty` >>
  simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def]
QED
Resume rb_compile_type_builtin_dispatch_body[bounds2]:
  Cases_on `type_bounds ret_ty` >>
  simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def]
QED
Resume rb_compile_type_builtin_dispatch_body[epsilon]:
  Cases_on `type_bounds ret_ty` >>
  simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def]
QED
Resume rb_compile_type_builtin_dispatch_body[convert]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value]) >> gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
  Cases_on `guard` >> simp[]
  >- simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def] >>
  qmatch_goalsub_abbrev_tac `if guard2 then _ else _` >>
  Cases_on `guard2` >> simp[] >- (irule rb_as_stack_val >>
    simp[rb_compile_bytestring_widen_copy]) >>
  Cases_on `ret_ty` >> simp[] >> irule rb_as_stack_val >>
  simp[rb_compile_type_convert]
QED
Resume rb_compile_type_builtin_dispatch_body[empty]:
  Cases_on `is_word_type ret_ty` >> simp[]
  >- simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` rb_step_let))) >>
  BETA_TAC >> conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_builtin_empty_complex]) >>
  simp[rb_step_def, rb_value_ok_def, rb_base_ptr]
QED
Resume rb_compile_type_builtin_dispatch_body[extract]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)`
      (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_bytestring_src]) >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_extract32_load]) >> gen_tac >> strip_tac >>
  irule rb_as_stack_val >> simp[rb_compile_clamp_basetype]
QED
Resume rb_compile_type_builtin_dispatch_body[encode]:
  Cases_on `LENGTH args = 1 /\ ~b` >> simp[]
  >- suspend "encode_single"
  >> suspend "encode_tuple"
QED
Resume rb_compile_type_builtin_dispatch_body[decode]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_unwrap_value]) >> gen_tac >> strip_tac >>
  irule rb_as_ptr_val >> irule rb_lower_abi_decode >> simp[rb_abi_decode]
QED
Resume rb_compile_type_builtin_dispatch_body[encode_single]:
  Cases_on `is_word_type (expr_type (HD args))` >> simp[]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_lower_value]) >> gen_tac >> strip_tac >>
      ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_compile_alloc_buffer]) >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `K T` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_emit_void]) >> gen_tac >>
      irule rb_as_ptr_val >> irule rb_lower_abi_encode >> simp[rb_abi_encode]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_unwrap_value]) >> gen_tac >> strip_tac >>
  irule rb_as_ptr_val >> irule rb_lower_abi_encode >> simp[rb_abi_encode]
QED
Resume rb_compile_type_builtin_dispatch_body[encode_tuple]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_operand_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_abi_encode_args]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_alloc_buffer]) >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` rb_step_let))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_store_abi_tuple, rb_every_zip_fst]) >> gen_tac >>
  irule rb_as_ptr_val >> irule rb_lower_abi_encode >> simp[rb_abi_encode]
QED
Finalise rb_compile_type_builtin_dispatch_body
