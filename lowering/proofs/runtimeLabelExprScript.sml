(* Expression compilation preserves reserved-operand exclusion. *)
Theory runtimeLabelExpr
Ancestors
  runtimeLabelExprCallbacks runtimeLabelExprPrimitives runtimeLabelPrimitives
  runtimeLabelBuiltinCore runtimeLabelBuiltinSystem runtimeLabelBuiltinArithmetic runtimeLabelBuiltins runtimeLabelABI runtimeLabelInvariant runtimeLabelValues
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
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
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
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >>
  BETA_TAC >> conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_builtin_empty_complex]) >>
  simp[rb_step_def, rb_value_ok_def, rb_base_ptr]
QED
Resume rb_compile_type_builtin_dispatch_body[extract]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_bytestring_src]) >>
  PairCases >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
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
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_unwrap_value]) >> gen_tac >> strip_tac >>
  irule rb_as_ptr_val >> irule rb_lower_abi_decode >> simp[rb_abi_decode]
QED
Resume rb_compile_type_builtin_dispatch_body[encode_single]:
  Cases_on `is_word_type (expr_type (HD args))` >> simp[]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_lower_value]) >> gen_tac >> strip_tac >>
      ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_compile_alloc_buffer]) >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_emit_void]) >> gen_tac >>
      irule rb_as_ptr_val >> irule rb_lower_abi_encode >> simp[rb_abi_encode]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_unwrap_value]) >> gen_tac >> strip_tac >>
  irule rb_as_ptr_val >> irule rb_lower_abi_encode >> simp[rb_abi_encode]
QED
Resume rb_compile_type_builtin_dispatch_body[encode_tuple]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_abi_encode_args]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_alloc_buffer]) >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_store_abi_tuple, rb_every_zip_fst]) >> gen_tac >>
  irule rb_as_ptr_val >> irule rb_lower_abi_encode >> simp[rb_abi_encode]
QED
Finalise rb_compile_type_builtin_dispatch_body

Theorem rb_compile_builtin_dispatch_body:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) ==>
  rb_step rb_value_ok
    (compile_builtin_dispatch_body cfn ce ret_ty ty bi args)
Proof
  strip_tac >> Cases_on `bi` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_builtin_dispatch_body_def, LET_THM] >>
  BETA_TAC >> simp_tac (srw_ss()) []
  >~ [`compile_builtin_calldatasize`] >- (irule rb_as_stack_val >> simp[rb_compile_builtin_calldatasize])
  >~ [`compile_env_var`] >- (irule rb_as_stack_val >> simp[rb_compile_env_var])
  >~ [`compile_acc`] >- (irule rb_as_stack_val >> simp[rb_compile_acc])
  >~ [`compile_neg`] >- suspend "neg"
  >~ [`compile_builtin_abs`] >- suspend "abs"
  >~ [`compile_blockhash`] >- suspend "blockhash"
  >~ [`compile_blobhash`] >- suspend "blobhash"
  >~ [`compile_floor`] >- suspend "floor"
  >~ [`compile_ceil`] >- suspend "ceil"
  >~ [`compile_uint2str`] >- suspend "uint2str"
  >~ [`compile_slice_calldata`] >- suspend "calldata"
  >~ [`compile_addmod`] >- suspend "addmod"
  >~ [`compile_mulmod`] >- suspend "mulmod"
  >~ [`compile_pow_mod256`] >- suspend "pow"
  >~ [`compile_ecrecover`] >- suspend "ecrecover"
  >~ [`compile_ecadd_points`] >- suspend "ecadd"
  >~ [`compile_ecmul_point`] >- suspend "ecmul"
  >~ [`compile_concat`] >- suspend "concat"
  >~ [`compile_slice_code`] >- suspend "slice"
  >~ [`compile_keccak256_bytes`] >- suspend "keccak"
  >~ [`compile_sha256_bytes`] >- suspend "sha"
  >~ [`compile_method_id_runtime`] >- suspend "method"
  >~ [`compile_as_wei_value_int`] >- suspend "wei"
  >~ [`compile_invert`] >- suspend "not"
  >~ [`compile_builtin_len`] >- suspend "len"
  >~ [`compile_make_tuple`] >- suspend "array"
  >> suspend "bop"
QED

Resume rb_compile_builtin_dispatch_body[neg]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_neg]
QED
Resume rb_compile_builtin_dispatch_body[abs]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_builtin_abs]
QED
Resume rb_compile_builtin_dispatch_body[blockhash]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_blockhash]
QED
Resume rb_compile_builtin_dispatch_body[blobhash]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_blobhash]
QED
Resume rb_compile_builtin_dispatch_body[floor]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_floor]
QED
Resume rb_compile_builtin_dispatch_body[ceil]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_ceil]
QED
Resume rb_compile_builtin_dispatch_body[uint2str]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_ptr_val >> simp[rb_compile_uint2str]
QED
Resume rb_compile_builtin_dispatch_body[calldata]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_ptr_val >> simp[rb_compile_slice_calldata, rb_operand_ok_def]
QED

Resume rb_compile_builtin_dispatch_body[addmod]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val >> simp[rb_compile_addmod]
QED
Resume rb_compile_builtin_dispatch_body[mulmod]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val >> simp[rb_compile_mulmod]
QED
Resume rb_compile_builtin_dispatch_body[pow]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val >> simp[rb_compile_pow_mod256]
QED
Resume rb_compile_builtin_dispatch_body[ecrecover]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val >> simp[rb_compile_ecrecover]
QED
Resume rb_compile_builtin_dispatch_body[not]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
  irule rb_as_stack_val >> simp[rb_emit_op, rb_compile_invert]
QED
Resume rb_compile_builtin_dispatch_body[wei]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> Cases_on `is_decimal_type (expr_type (HD args))` >> simp[] >>
  irule rb_as_stack_val >> simp[rb_compile_as_wei_value_decimal, rb_compile_as_wei_value_int]
QED
Resume rb_compile_builtin_dispatch_body[len]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >>
  irule rb_compile_builtin_len >>
  gvs[rb_env_ok_def, rb_value_operand]
QED
Resume rb_compile_builtin_dispatch_body[ecadd]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_unwrap_value]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_unwrap_value]) >>
  gen_tac >> strip_tac >> irule rb_as_ptr_val >> simp[rb_compile_ecadd_points]
QED
Resume rb_compile_builtin_dispatch_body[ecmul]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_unwrap_value, rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val >> simp[rb_compile_ecmul_point]
QED
Resume rb_compile_builtin_dispatch_body[keccak]:
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  rpt CASE_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >>
  simp[rb_compile_keccak256_bytes, rb_compile_keccak256_bytesm, rb_compile_keccak256_word]
QED
Resume rb_compile_builtin_dispatch_body[sha]:
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  rpt CASE_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >>
  simp[rb_compile_sha256_bytes, rb_compile_sha256_bytesm, rb_compile_sha256_word]
QED
Resume rb_compile_builtin_dispatch_body[method]:
  Cases_on `method_id_literal (HD args)` >> simp[]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
      (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
      gen_tac >> strip_tac >> Cases_on `ret_ty = BaseT (BytesT (Fixed 4))` >> simp[]
      >- (irule rb_as_stack_val >> simp[rb_compile_method_id_runtime]) >>
      irule rb_as_ptr_val >> simp[rb_compile_method_id_runtime]) >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_literal_vv]
QED
Resume rb_compile_builtin_dispatch_body[array]:
  Cases_on `o'` >> simp[] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer])) >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >> irule rb_as_ptr_val >>
  simp[rb_compile_make_tuple, rb_compile_make_array]
QED
Resume rb_compile_builtin_dispatch_body[concat]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer]) >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_op, rb_operand_ok_def]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer]) >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_void, rb_operand_ok_def]) >>
  gen_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_concat]) >>
  gen_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_void]) >>
  simp[rb_step_def, rb_value_ok_def, rb_base_ptr, rb_buffer_ok_def]
QED
Resume rb_compile_builtin_dispatch_body[slice]:
  Cases_on `is_self_code (HD args)` >> simp[] >- suspend "slice_code" >>
  Cases_on `is_extcode (HD args)` >> simp[] >- suspend "slice_ext" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value]) >>
  gen_tac >> strip_tac >> Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[]
  >- suspend "slice_bytes" >> suspend "slice_fixed"
QED
Resume rb_compile_builtin_dispatch_body[slice_code]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val >> simp[rb_compile_slice_code]
QED
Resume rb_compile_builtin_dispatch_body[slice_ext]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val >> simp[rb_compile_slice_extcode]
QED
Resume rb_compile_builtin_dispatch_body[slice_bytes]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_bytestring_src]) >>
  PairCases >> simp[] >> strip_tac >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val >> simp[rb_compile_slice_data]
QED
Resume rb_compile_builtin_dispatch_body[slice_fixed]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer]) >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_void]) >>
  gen_tac >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val >> simp[rb_compile_slice_data, rb_operand_ok_def]
QED
Resume rb_compile_builtin_dispatch_body[bop]:
  qmatch_goalsub_abbrev_tac `if membership then _ else _` >>
  Cases_on `membership` >> simp[] >- suspend "membership" >>
  qmatch_goalsub_abbrev_tac `if hashing then _ else _` >>
  Cases_on `hashing` >> simp[] >- suspend "hashing" >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val >> simp[rb_compile_binop]
QED
Resume rb_compile_builtin_dispatch_body[membership]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value]) >>
  gen_tac >> strip_tac >> rpt CASE_TAC
  >>~- ([`compile_multi_exprs`], suspend "membership_list") >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_compile_var_array_membership]
QED
Resume rb_compile_builtin_dispatch_body[membership_list]:
  markerLib.RESUME_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_multi_exprs])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >>
  simp[rb_compile_list_membership_in, rb_compile_list_membership_notin]
QED

Theorem rb_literal_or_bytestring_hash[local]:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) ==>
  rb_step rb_operand_ok (\st.
    case bytestring_literal_hash e of
      SOME h => (Lit h, st)
    | NONE => UNCURRY compile_bytestring_hash (lower_value cfn ce ty e st))
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e` >> simp[pairTheory.UNCURRY_DEF]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value]) >>
      gen_tac >> strip_tac >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_bytestring_hash]) >>
  simp[rb_step_def, rb_operand_ok_def]
QED
Resume rb_compile_builtin_dispatch_body[hashing]:
  ntac 2 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> irule (SIMP_RULE (srw_ss()) [LET_THM, pairTheory.UNCURRY_DEF] rb_literal_or_bytestring_hash) >> simp[])) >>
    gen_tac >> strip_tac) >>
  Cases_on `b = Eq` >> simp[]
  >- (irule rb_as_stack_val >> simp[rb_emit_op]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >> simp[rb_emit_op]
QED
Finalise rb_compile_builtin_dispatch_body

Theorem rb_compile_expr_body:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) /\
  (!env ret_ty ty bi args. rb_env_ok env ==> rb_step rb_value_ok (bfn env ret_ty ty bi args)) /\
  (!env vv_ty ty tb ret_ty args. rb_env_ok env ==> rb_step rb_value_ok (tfn env vv_ty ty tb ret_ty args)) ==>
  rb_step rb_value_ok (compile_expr_body cfn bfn tfn ce ty e)
Proof
  strip_tac >> Cases_on `e` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_expr_body_def, LET_THM] >> BETA_TAC >>
  simp_tac (srw_ss()) []
  >~ [`compile_literal_vv`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_literal_vv])
  >~ [`compile_name_vv`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_name_vv])
  >~ [`compile_subscript`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_subscript])
  >~ [`compile_attribute`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_attribute])
  >~ [`compile_call`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> irule rb_compile_call >> simp[rb_abi_encode, rb_abi_decode])
  >~ [`rb_step rb_value_ok (\st. tfn _ _ _ _ _ _ st)`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[])
  >~ [`compile_struct_lit`] >- suspend "struct"
  >~ [`compile_dynarray_pop`] >- suspend "pop"
  >~ [`lower_value`] >- suspend "ifexp"
  >~ [`FLOOKUP ce.ce_module_vars`] >- suspend "top"
  >~ [`ce.ce_flag_member_id`] >- simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def]
  >> suspend "builtin"
QED
Resume rb_compile_expr_body[builtin]:
  Cases_on `b` >> simp[] >>
  namedCases_on `l` ["", "a0 xs0"] >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[] >>
  Cases_on `a0` >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[] >>
  namedCases_on `xs0` ["", "a1 xs1"] >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[] >>
  Cases_on `a1` >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[] >>
  namedCases_on `xs1` ["", "a2 xs2"] >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_powmod256_names] >>
  Cases_on `a2` >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[] >>
  Cases_on `xs2` >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  simp[cj 1 rb_compile_mod_names, cj 2 rb_compile_mod_names]
QED

Resume rb_compile_expr_body[struct]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_struct_lit >> gvs[rb_buffer_ok_def]) >>
  simp[rb_step_def, rb_value_ok_def, rb_base_ptr]
QED
Resume rb_compile_expr_body[pop]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok o FST` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> irule rb_compile_get_target_ptr >> simp[]) >>
  gen_tac >> strip_tac >> pairarg_tac >> gvs[] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_dynarray_pop >> gvs[rb_env_ok_def]) >>
  simp[rb_step_def, rb_value_ok_def, rb_mk_ptr]
QED

Resume rb_compile_expr_body[top]:
  rpt CASE_TAC >> simp[]
  >>~- ([`rb_step rb_value_ok (\st. (LocatedValue _ _,st))`],
    simp[rb_step_def, rb_value_ok_def, rb_mk_ptr, rb_operand_ok_def]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_inst])) >>
  simp[rb_step_def, rb_value_ok_def, rb_operand_ok_def]
QED
Resume rb_compile_expr_body[ifexp]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_fresh_var]) >>
  gen_tac >>
  ntac 3 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(\l. rb_operand_ok (Label l))` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[SRULE [rb_operand_ok_def] rb_fresh_label])) >>
    gen_tac >> strip_tac) >>
  ntac 2 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      simp[rb_emit_inst, rb_new_block, rb_operand_ok_def])) >> gen_tac) >>
  ntac 2 (
    ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[])) >>
    gen_tac >> strip_tac >>
    ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_ifexp_arm])) >>
    gen_tac >> strip_tac >>
    ntac 3 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
      (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_emit_inst, rb_new_block, rb_operand_ok_def])) >> gen_tac)) >>
  Cases_on `is_word_type (expr_type (IfExp t e' e0 e1))` >>
  simp[rb_step_def, rb_value_ok_def, rb_mk_ptr, rb_operand_ok_def]
QED

Finalise rb_compile_expr_body

Theorem rb_compile_expr_raw:
  (!ce ty e st. rb_env_ok ce /\ rb_state_ok st ==>
    rb_state_ok (SND (compile_expr ce ty e st)) /\
    rb_value_ok (FST (compile_expr ce ty e st))) /\
  (!ce rt ty bi args st. rb_env_ok ce /\ rb_state_ok st ==>
    rb_state_ok (SND (compile_builtin_dispatch ce rt ty bi args st)) /\
    rb_value_ok (FST (compile_builtin_dispatch ce rt ty bi args st))) /\
  (!ce vt ty tb rt args st. rb_env_ok ce /\ rb_state_ok st ==>
    rb_state_ok (SND (compile_type_builtin_dispatch ce vt ty tb rt args st)) /\
    rb_value_ok (FST (compile_type_builtin_dispatch ce vt ty tb rt args st)))
Proof
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type"
QED

Resume rb_compile_expr_raw[expr]:
  `rb_expr_callback (expr_size e) compile_expr` by
    (rw[rb_expr_callback_def, rb_step_def] >> pairarg_tac >> gvs[] >>
     first_x_assum drule >> disch_then drule_all >>
     disch_then (qspec_then `ty` mp_tac) >> simp[]) >>
  `rb_builtin_callback (expr_size e) compile_builtin_dispatch` by
    (rw[rb_builtin_callback_def, rb_step_def] >> pairarg_tac >> gvs[] >>
     qpat_x_assum `!args ce rt ty bi st. _ ==> _ ==> rb_state_ok (SND (compile_builtin_dispatch ce rt ty bi args st)) /\ _` drule >>
     disch_then drule_all >>
     disch_then (qspecl_then [`ret_ty`, `ty`, `bi`] mp_tac) >> simp[]) >>
  `rb_type_callback (expr_size e) compile_type_builtin_dispatch` by
    (rw[rb_type_callback_def, rb_step_def] >> pairarg_tac >> gvs[] >>
     qpat_x_assum `!args ce vt ty tb rt st. _ ==> _ ==> rb_state_ok (SND (compile_type_builtin_dispatch ce vt ty tb rt args st)) /\ _` drule >>
     disch_then drule_all >>
     disch_then (qspecl_then [`vv_ty`, `ty`, `tb`, `ret_ty`] mp_tac) >> simp[]) >>
  strip_tac >>
  `rb_step rb_value_ok
    (compile_expr_body (expr_child_callback (expr_size e) compile_expr)
      (builtin_child_callback (expr_size e) compile_builtin_dispatch)
      (type_child_callback (expr_size e) compile_type_builtin_dispatch) ce ty e)` by
    (irule rb_compile_expr_body >> simp[rb_expr_child_callback,
      rb_builtin_child_callback, rb_type_child_callback]) >>
  ONCE_REWRITE_TAC[compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[rb_step_def] >> first_x_assum drule >>
  pairarg_tac >> gvs[]
QED

Resume rb_compile_expr_raw[builtin]:
  `rb_expr_callback (list_size expr_size args) compile_expr` by
    (rw[rb_expr_callback_def, rb_step_def] >> pairarg_tac >> gvs[] >>
     first_x_assum drule >> disch_then drule_all >>
     disch_then (qspec_then `ty` mp_tac) >> simp[]) >>
  strip_tac >>
  `rb_step rb_value_ok
    (compile_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args) compile_expr)
      ce rt ty bi args)` by
    (irule rb_compile_builtin_dispatch_body >> simp[rb_expr_child_callback]) >>
  ONCE_REWRITE_TAC[compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[rb_step_def] >> first_x_assum drule >> pairarg_tac >> gvs[]
QED

Resume rb_compile_expr_raw[type]:
  `rb_expr_callback (list_size expr_size args) compile_expr` by
    (rw[rb_expr_callback_def, rb_step_def] >> pairarg_tac >> gvs[] >>
     first_x_assum drule >> disch_then drule_all >>
     disch_then (qspec_then `ty'` mp_tac) >> simp[]) >>
  strip_tac >>
  `rb_step rb_value_ok
    (compile_type_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args) compile_expr)
      ce vt ty tb rt args)` by
    (irule rb_compile_type_builtin_dispatch_body >> simp[rb_expr_child_callback]) >>
  ONCE_REWRITE_TAC[compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[rb_step_def] >> first_x_assum drule >> pairarg_tac >> gvs[]
QED

Finalise rb_compile_expr_raw

Theorem compile_expr_no_runtime_begin:
  rb_expr_contract
Proof
  mp_tac rb_compile_expr_raw >>
  simp[rb_expr_contract_def, rb_step_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> metis_tac[pairTheory.FST, pairTheory.SND]
QED
