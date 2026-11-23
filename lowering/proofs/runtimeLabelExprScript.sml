(* Expression compilation preserves reserved-operand exclusion. *)
Theory runtimeLabelExpr
Ancestors
  listZipProps
  runtimeLabelExprCallbacks runtimeLabelExprPrimitives runtimeLabelPrimitives
  runtimeLabelBuiltinCore runtimeLabelBuiltinSystem runtimeLabelBuiltinArithmetic runtimeLabelBuiltins runtimeLabelABI runtimeLabelInvariant runtimeLabelValues
  runtimeLabelBoolChain
  exprLowering exprLoweringProps exprCallBounds

Theorem rb_as_ptr_val_for[local]:
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) m ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (\st. as_ptr_val ty loc (m st))
Proof
  simp[rb_step_for_def] >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> Cases_on `m st` >>
  simp[as_ptr_val_def, rb_value_ok_for_def, rb_mk_ptr_for]
QED

Theorem rb_abi_encode_payload_for[local]:
  rb_env_ok_for source_checks ce /\ EVERY (rb_value_ok_for source_checks) vs /\
  (single ==> vs <> []) /\ rb_operand_ok_for source_checks dst ==>
  rb_step_for source_checks (rb_operand_ok_for source_checks)
    (compile_abi_encode_payload ce single vs tys dst)
Proof
  strip_tac >> Cases_on `single` >> simp[compile_abi_encode_payload_def]
  >- (Cases_on `vs` >> gvs[] >>
      irule rb_step_bind_for >> qexists_tac `rb_operand_ok_for source_checks` >>
      simp[rb_unwrap_value_for] >> gen_tac >> strip_tac >>
      IF_CASES_TAC >> simp[rb_abi_encode_for] >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
      simp[rb_emit_void_for, rb_step_return_for]) >>
  simp[rb_compile_abi_encode_values_to_buf_for, rb_abi_encode_for, EVERY_FST_ZIP]
QED

Theorem rb_compile_type_builtin_dispatch_body_for[local]:
  (rb_env_ok_for source_checks) ce /\
  (!env ty e. (rb_env_ok_for source_checks) env ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks)
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

Resume rb_compile_type_builtin_dispatch_body_for[bounds]:
  Cases_on `type_bounds ret_ty` >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def]
QED
Resume rb_compile_type_builtin_dispatch_body_for[bounds2]:
  Cases_on `type_bounds ret_ty` >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def]
QED
Resume rb_compile_type_builtin_dispatch_body_for[epsilon]:
  Cases_on `type_bounds ret_ty` >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def]
QED
Resume rb_compile_type_builtin_dispatch_body_for[convert]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value_for]) >> gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
  Cases_on `guard` >> simp[]
  >- simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def] >>
  qmatch_goalsub_abbrev_tac `if guard2 then _ else _` >>
  Cases_on `guard2` >> simp[] >- (irule rb_as_ptr_val_for >>
    simp[rb_compile_bytestring_widen_copy_for]) >>
  qmatch_goalsub_abbrev_tac `if memory_result then _ else _` >>
  Cases_on `memory_result` >> simp[] >- (irule rb_as_ptr_val_for >>
    simp[rb_compile_type_convert_for]) >>
  Cases_on `ret_ty` >> simp[] >> irule rb_as_stack_val_for >>
  simp[rb_compile_type_convert_for]
QED
Resume rb_compile_type_builtin_dispatch_body_for[empty]:
  Cases_on `is_word_type ret_ty` >> simp[]
  >- simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >>
  BETA_TAC >> conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_builtin_empty_complex_for]) >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_base_ptr_for]
QED
Resume rb_compile_type_builtin_dispatch_body_for[extract]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value_for]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. (rb_operand_ok_for source_checks) (FST p) /\ (rb_operand_ok_for source_checks) (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_bytestring_src_for]) >>
  PairCases >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_lower_value_for]) >> gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_compile_extract32_load_for]) >> gen_tac >> strip_tac >>
  irule rb_as_stack_val_for >> simp[rb_compile_clamp_basetype_for]
QED
Resume rb_compile_type_builtin_dispatch_body_for[encode]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\vs. EVERY (rb_value_ok_for source_checks) vs /\ LENGTH vs = LENGTH (args:expr list)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV
        (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def))))
        rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac
  >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      `rb_step_for source_checks (EVERY (rb_value_ok_for source_checks))
        (compile_abi_encode_args cfn ce args)` by
        (irule rb_compile_abi_encode_args_for >> simp[]) >>
      pop_assum mp_tac >> simp[rb_step_for_def] >> strip_tac >> rpt strip_tac >>
      pairarg_tac >> gvs[] >>
      first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
      qspec_then `st` mp_tac (Q.SPECL [`args`, `cfn`, `ce`]
        compile_abi_encode_args_length) >> simp[]) >>
  gen_tac >> strip_tac >>
  irule rb_as_ptr_val_for >> irule rb_lower_abi_encode_for >>
  rpt strip_tac >> irule rb_abi_encode_payload_for >> simp[] >>
  Cases_on `vs` >> gvs[]
QED
Resume rb_compile_type_builtin_dispatch_body_for[decode]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    simp[rb_unwrap_value_for]) >> gen_tac >> strip_tac >>
  irule rb_as_ptr_val_for >> irule rb_lower_abi_decode_for >> simp[rb_abi_decode_for]
QED
Finalise rb_compile_type_builtin_dispatch_body_for

Theorem rb_compile_builtin_dispatch_body_for[local]:
  (rb_env_ok_for source_checks) ce /\
  (!env ty e. (rb_env_ok_for source_checks) env ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_builtin_dispatch_body cfn ce ret_ty ty bi args)
Proof
  strip_tac >> Cases_on `bi` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_builtin_dispatch_body_def, LET_THM] >>
  BETA_TAC >> simp_tac (srw_ss()) []
  >~ [`compile_builtin_calldatasize`] >- (irule rb_as_stack_val_for >> simp[rb_compile_builtin_calldatasize_for])
  >~ [`compile_env_var`] >- (irule rb_as_stack_val_for >> simp[rb_compile_env_var_for])
  >~ [`compile_acc`] >- (irule rb_as_stack_val_for >> simp[rb_compile_acc_for])
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
  >~ [`as_ptr_val _ LocMemory ((case _ of Label _ => _ | _ => _), _)`] >-
    suspend "namedconst"
  >~ [`compile_bool_chain_ops`] >- suspend "boolchain"
  >> suspend "bop"
QED

Resume rb_compile_builtin_dispatch_body_for[neg]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_neg_for]
QED
Resume rb_compile_builtin_dispatch_body_for[abs]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_builtin_abs_for]
QED
Resume rb_compile_builtin_dispatch_body_for[blockhash]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_blockhash_for]
QED
Resume rb_compile_builtin_dispatch_body_for[blobhash]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_blobhash_for]
QED
Resume rb_compile_builtin_dispatch_body_for[floor]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_floor_for]
QED
Resume rb_compile_builtin_dispatch_body_for[ceil]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_ceil_for]
QED
Resume rb_compile_builtin_dispatch_body_for[uint2str]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_ptr_val_for >> simp[rb_compile_uint2str_for]
QED
Resume rb_compile_builtin_dispatch_body_for[calldata]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_ptr_val_for >> simp[rb_compile_slice_calldata_for, rb_operand_ok_for_def]
QED

Resume rb_compile_builtin_dispatch_body_for[addmod]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val_for >> simp[rb_compile_addmod_for]
QED
Resume rb_compile_builtin_dispatch_body_for[mulmod]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val_for >> simp[rb_compile_mulmod_for]
QED
Resume rb_compile_builtin_dispatch_body_for[pow]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val_for >> simp[rb_compile_pow_mod256_for]
QED
Resume rb_compile_builtin_dispatch_body_for[ecrecover]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val_for >> simp[rb_compile_ecrecover_for]
QED
Resume rb_compile_builtin_dispatch_body_for[not]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
  irule rb_as_stack_val_for >> simp[rb_emit_op_for, rb_compile_invert_for]
QED
Resume rb_compile_builtin_dispatch_body_for[wei]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> Cases_on `is_decimal_type (expr_type (HD args))` >> simp[] >>
  irule rb_as_stack_val_for >> simp[rb_compile_as_wei_value_decimal_for, rb_compile_as_wei_value_int_for]
QED
Resume rb_compile_builtin_dispatch_body_for[len]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >>
  irule rb_compile_builtin_len_for >>
  gvs[rb_env_ok_for_def, rb_value_operand_for]
QED
Resume rb_compile_builtin_dispatch_body_for[ecadd]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_unwrap_value_for]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_unwrap_value_for]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_ecadd_points_for]
QED
Resume rb_compile_builtin_dispatch_body_for[ecmul]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[]) >>
  gen_tac >> strip_tac >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_unwrap_value_for, rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val_for >> simp[rb_compile_ecmul_point_for]
QED
Resume rb_compile_builtin_dispatch_body_for[keccak]:
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  rpt CASE_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >>
  simp[rb_compile_keccak256_bytes_for, rb_compile_keccak256_bytesm_for, rb_compile_keccak256_word_for]
QED
Resume rb_compile_builtin_dispatch_body_for[sha]:
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  rpt CASE_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >>
  simp[rb_compile_sha256_bytes_for, rb_compile_sha256_bytesm_for, rb_compile_sha256_word_for]
QED
Resume rb_compile_builtin_dispatch_body_for[method]:
  Cases_on `method_id_literal (HD args)` >> simp[]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
      (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
      gen_tac >> strip_tac >> Cases_on `ret_ty = BaseT (BytesT (Fixed 4))` >> simp[]
      >- (irule rb_as_stack_val_for >> simp[rb_compile_method_id_runtime_for]) >>
      irule rb_as_ptr_val_for >> simp[rb_compile_method_id_runtime_for]) >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_literal_vv_for]
QED
Resume rb_compile_builtin_dispatch_body_for[array]:
  Cases_on `o'` >> simp[] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer_for])) >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >> irule rb_as_ptr_val_for >>
  simp[rb_compile_make_tuple_for, rb_compile_make_array_for]
QED
Resume rb_compile_builtin_dispatch_body_for[concat]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer_for]) >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_op_for, rb_operand_ok_for_def]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer_for]) >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_void_for, rb_operand_ok_for_def]) >>
  gen_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_concat_for]) >>
  gen_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_op_for]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_void_for]) >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_base_ptr_for, rb_buffer_ok_for_def]
QED
Resume rb_compile_builtin_dispatch_body_for[slice]:
  Cases_on `is_self_code (HD args)` >> simp[] >- suspend "slice_code" >>
  Cases_on `is_extcode (HD args)` >> simp[] >- suspend "slice_ext" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for]) >>
  gen_tac >> strip_tac >> Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[]
  >- suspend "slice_bytes" >> suspend "slice_fixed"
QED
Resume rb_compile_builtin_dispatch_body_for[slice_code]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val_for >> simp[rb_compile_slice_code_for]
QED
Resume rb_compile_builtin_dispatch_body_for[slice_ext]:
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val_for >> simp[rb_compile_slice_extcode_for]
QED
Resume rb_compile_builtin_dispatch_body_for[slice_bytes]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. (rb_operand_ok_for source_checks) (FST p) /\ (rb_operand_ok_for source_checks) (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_bytestring_src_for]) >>
  PairCases >> simp[] >> strip_tac >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val_for >> simp[rb_compile_slice_data_for]
QED
Resume rb_compile_builtin_dispatch_body_for[slice_fixed]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer_for]) >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_void_for]) >>
  gen_tac >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_ptr_val_for >> simp[rb_compile_slice_data_for, rb_operand_ok_for_def]
QED
Resume rb_compile_builtin_dispatch_body_for[bop]:
  qmatch_goalsub_abbrev_tac `if membership then _ else _` >>
  Cases_on `membership` >> simp[] >- suspend "membership" >>
  qmatch_goalsub_abbrev_tac `if hashing then _ else _` >>
  Cases_on `hashing` >> simp[] >- suspend "hashing" >>
  rpt (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for])) >>
    gen_tac >> strip_tac) >>
  irule rb_as_stack_val_for >> simp[rb_compile_binop_for]
QED
Resume rb_compile_builtin_dispatch_body_for[membership]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for]) >>
  gen_tac >> strip_tac >> rpt CASE_TAC
  >>~- ([`compile_multi_exprs`], suspend "membership_list") >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_compile_var_array_membership_for]
QED
Resume rb_compile_builtin_dispatch_body_for[membership_list]:
  markerLib.RESUME_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY (rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_multi_exprs_for])) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >>
  simp[rb_compile_list_membership_in_for, rb_compile_list_membership_notin_for]
QED

Theorem rb_literal_or_bytestring_hash_for[local]:
  (rb_env_ok_for source_checks) ce /\
  (!env ty e. (rb_env_ok_for source_checks) env ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env ty e)) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (\st.
    case bytestring_literal_hash e of
      SOME h => (Lit h, st)
    | NONE => UNCURRY compile_bytestring_hash (lower_value cfn ce ty e st))
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e` >> simp[pairTheory.UNCURRY_DEF]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for]) >>
      gen_tac >> strip_tac >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_bytestring_hash_for]) >>
  simp[rb_step_for_def, rb_operand_ok_for_def]
QED
Resume rb_compile_builtin_dispatch_body_for[hashing]:
  ntac 2 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> irule (SIMP_RULE (srw_ss()) [LET_THM, pairTheory.UNCURRY_DEF] rb_literal_or_bytestring_hash_for) >> simp[])) >>
    gen_tac >> strip_tac) >>
  Cases_on `b = Eq` >> simp[]
  >- (irule rb_as_stack_val_for >> simp[rb_emit_op_for]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_op_for]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >> simp[rb_emit_op_for]
QED
Resume rb_compile_builtin_dispatch_body_for[namedconst]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok_for source_checks` (Q.GEN `P`
      (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC
        ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >>
  BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for]) >>
  gen_tac >> strip_tac >>
  rename1 `rb_operand_ok_for source_checks op` >>
  Cases_on `is_word_type ret_ty` >> Cases_on `op` >>
  simp[rb_step_for_def, as_stack_val_def, as_ptr_val_def,
       rb_value_ok_for_def, rb_mk_ptr_for, rb_operand_ok_for_def]
QED

Resume rb_compile_builtin_dispatch_body_for[boolchain]:
  let
    fun bind_step pred =
      ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.ISPEC pred (Q.GEN `P`
          (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC
            ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >>
      BETA_TAC
    val normalize = CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV))
  in
    bind_step `K T` >> conj_tac >- (normalize >> simp[rb_fresh_var_for]) >>
    gen_tac >>
    bind_step `\l. rb_operand_ok_for source_checks (Label l)` >>
    conj_tac >- (normalize >> simp[SRULE [rb_operand_ok_for_def] rb_fresh_label_for]) >>
    gen_tac >> strip_tac >>
    bind_step `K T` >> conj_tac >-
      (normalize >> irule rb_compile_bool_chain_ops_for >> simp[rb_lower_value_for]) >>
    gen_tac >>
    bind_step `K T` >> conj_tac >- (normalize >> simp[rb_new_block_for]) >>
    simp[rb_step_for_def, rb_value_ok_for_def]
  end
QED
Finalise rb_compile_builtin_dispatch_body_for

Theorem rb_compile_expr_body_for[local]:
  (rb_env_ok_for source_checks) ce /\
  (!env ty e. (rb_env_ok_for source_checks) env ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env ty e)) /\
  (!env ret_ty ty bi args. (rb_env_ok_for source_checks) env ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (bfn env ret_ty ty bi args)) /\
  (!env vv_ty ty tb ret_ty args. (rb_env_ok_for source_checks) env ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (tfn env vv_ty ty tb ret_ty args)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_expr_body cfn bfn tfn ce ty e)
Proof
  strip_tac >> Cases_on `e` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_expr_body_def, LET_THM] >> BETA_TAC >>
  simp_tac (srw_ss()) []
  >~ [`compile_literal_vv`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_literal_vv_for])
  >~ [`compile_name_vv`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_name_vv_for])
  >~ [`compile_subscript`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_subscript_for])
  >~ [`compile_attribute`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_attribute_for])
  >~ [`compile_call`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> irule rb_compile_call_for >> simp[rb_abi_encode_for, rb_abi_decode_for, rb_env_ok_without_defaults_for])
  >~ [`(rb_step_for source_checks) (rb_value_ok_for source_checks) (\st. tfn _ _ _ _ _ _ st)`] >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[])
  >~ [`compile_struct_lit`] >- suspend "struct"
  >~ [`compile_dynarray_pop`] >- suspend "pop"
  >~ [`lower_value`] >- suspend "ifexp"
  >~ [`FLOOKUP ce.ce_module_vars`] >- suspend "top"
  >~ [`ce.ce_flag_member_id`] >- simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def]
  >> suspend "builtin"
QED
Resume rb_compile_expr_body_for[builtin]:
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
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_powmod256_names_for] >>
  Cases_on `a2` >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[] >>
  Cases_on `xs2` >> simp[] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  simp[cj 1 rb_compile_mod_names_for, cj 2 rb_compile_mod_names_for]
QED

Resume rb_compile_expr_body_for[struct]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_alloc_buffer_for]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_struct_lit_for >> gvs[rb_buffer_ok_for_def]) >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_base_ptr_for]
QED
Resume rb_compile_expr_body_for[pop]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks) o FST` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> irule rb_compile_get_target_ptr_for >> simp[]) >>
  gen_tac >> strip_tac >> pairarg_tac >> gvs[] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_dynarray_pop_for >> gvs[rb_env_ok_for_def]) >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_mk_ptr_for]
QED

Resume rb_compile_expr_body_for[top]:
  rpt CASE_TAC >> simp[]
  >>~- ([`(rb_step_for source_checks) (rb_value_ok_for source_checks) (\st. (LocatedValue _ _,st))`],
    simp[rb_step_for_def, rb_value_ok_for_def, rb_mk_ptr_for, rb_operand_ok_for_def]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_emit_inst_for])) >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_operand_ok_for_def]
QED
Resume rb_compile_expr_body_for[ifexp]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_lower_value_for]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_fresh_var_for]) >>
  gen_tac >>
  ntac 3 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(\l. (rb_operand_ok_for source_checks) (Label l))` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[SRULE [rb_operand_ok_for_def] rb_fresh_label_for])) >>
    gen_tac >> strip_tac) >>
  ntac 2 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      simp[rb_emit_inst_for, rb_new_block_for, rb_operand_ok_for_def])) >> gen_tac) >>
  ntac 2 (
    ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[])) >>
    gen_tac >> strip_tac >>
    ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
    (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >> simp[rb_compile_ifexp_arm_for])) >>
    gen_tac >> strip_tac >>
    ntac 3 (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `K T` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV compileEnvTheory.comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
      (conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        simp[rb_emit_inst_for, rb_new_block_for, rb_operand_ok_for_def])) >> gen_tac)) >>
  Cases_on `is_word_type (expr_type (IfExp t e' e0 e1))` >>
  simp[rb_step_for_def, rb_value_ok_for_def, rb_mk_ptr_for, rb_operand_ok_for_def]
QED

Finalise rb_compile_expr_body_for

Theorem rb_compile_expr_raw_for[local]:
  (!ce ty e st. (rb_env_ok_for source_checks) ce /\ (rb_state_ok_for source_checks) st ==>
    (rb_state_ok_for source_checks) (SND (compile_expr ce ty e st)) /\
    (rb_value_ok_for source_checks) (FST (compile_expr ce ty e st))) /\
  (!ce rt ty bi args st. (rb_env_ok_for source_checks) ce /\ (rb_state_ok_for source_checks) st ==>
    (rb_state_ok_for source_checks) (SND (compile_builtin_dispatch ce rt ty bi args st)) /\
    (rb_value_ok_for source_checks) (FST (compile_builtin_dispatch ce rt ty bi args st))) /\
  (!ce vt ty tb rt args st. (rb_env_ok_for source_checks) ce /\ (rb_state_ok_for source_checks) st ==>
    (rb_state_ok_for source_checks) (SND (compile_type_builtin_dispatch ce vt ty tb rt args st)) /\
    (rb_value_ok_for source_checks) (FST (compile_type_builtin_dispatch ce vt ty tb rt args st)))
Proof
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type"
QED

Resume rb_compile_expr_raw_for[expr]:
  `(rb_expr_callback_for source_checks) (expr_size e + cenv_defaults_size ce) compile_expr` by
    (rw[rb_expr_callback_for_def, rb_step_for_def] >> pairarg_tac >> gvs[] >>
     first_x_assum drule >> disch_then drule_all >>
     disch_then (qspec_then `ty` mp_tac) >> simp[]) >>
  `(rb_builtin_callback_for source_checks) (expr_size e + cenv_defaults_size ce) compile_builtin_dispatch` by
    (rw[rb_builtin_callback_for_def, rb_step_for_def] >> pairarg_tac >> gvs[] >>
     qpat_x_assum `!args ce rt ty bi st. _ ==> _ ==> (rb_state_ok_for source_checks) (SND (compile_builtin_dispatch ce rt ty bi args st)) /\ _` drule >>
     disch_then drule_all >>
     disch_then (qspecl_then [`ret_ty`, `ty`, `bi`] mp_tac) >> simp[]) >>
  `(rb_type_callback_for source_checks) (expr_size e + cenv_defaults_size ce) compile_type_builtin_dispatch` by
    (rw[rb_type_callback_for_def, rb_step_for_def] >> pairarg_tac >> gvs[] >>
     qpat_x_assum `!args ce vt ty tb rt st. _ ==> _ ==> (rb_state_ok_for source_checks) (SND (compile_type_builtin_dispatch ce vt ty tb rt args st)) /\ _` drule >>
     disch_then drule_all >>
     disch_then (qspecl_then [`vv_ty`, `ty`, `tb`, `ret_ty`] mp_tac) >> simp[]) >>
  strip_tac >>
  `(rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_expr_body (expr_child_callback (expr_size e + cenv_defaults_size ce) compile_expr)
      (builtin_child_callback (expr_size e + cenv_defaults_size ce) compile_builtin_dispatch)
      (type_child_callback (expr_size e + cenv_defaults_size ce) compile_type_builtin_dispatch) ce ty e)` by
    (irule rb_compile_expr_body_for >> simp[rb_expr_child_callback_for,
      rb_builtin_child_callback_for, rb_type_child_callback_for]) >>
  ONCE_REWRITE_TAC[compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[rb_step_for_def] >> first_x_assum drule >>
  pairarg_tac >> gvs[]
QED

Resume rb_compile_expr_raw_for[builtin]:
  `(rb_expr_callback_for source_checks) (list_size expr_size args + cenv_defaults_size ce) compile_expr` by
    (rw[rb_expr_callback_for_def, rb_step_for_def] >> pairarg_tac >> gvs[] >>
     first_x_assum drule >> disch_then drule_all >>
     disch_then (qspec_then `ty` mp_tac) >> simp[]) >>
  strip_tac >>
  `(rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args + cenv_defaults_size ce) compile_expr)
      ce rt ty bi args)` by
    (irule rb_compile_builtin_dispatch_body_for >> simp[rb_expr_child_callback_for]) >>
  ONCE_REWRITE_TAC[compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[rb_step_for_def] >> first_x_assum drule >> pairarg_tac >> gvs[]
QED

Resume rb_compile_expr_raw_for[type]:
  `(rb_expr_callback_for source_checks) (list_size expr_size args + cenv_defaults_size ce) compile_expr` by
    (rw[rb_expr_callback_for_def, rb_step_for_def] >> pairarg_tac >> gvs[] >>
     first_x_assum drule >> disch_then drule_all >>
     disch_then (qspec_then `ty'` mp_tac) >> simp[]) >>
  strip_tac >>
  `(rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_type_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args + cenv_defaults_size ce) compile_expr)
      ce vt ty tb rt args)` by
    (irule rb_compile_type_builtin_dispatch_body_for >> simp[rb_expr_child_callback_for]) >>
  ONCE_REWRITE_TAC[compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[rb_step_for_def] >> first_x_assum drule >> pairarg_tac >> gvs[]
QED

Finalise rb_compile_expr_raw_for

Theorem compile_expr_label_checks:
  (rb_expr_contract_for source_checks)
Proof
  mp_tac rb_compile_expr_raw_for >>
  simp[rb_expr_contract_for_def, rb_step_for_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> metis_tac[pairTheory.FST, pairTheory.SND]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_as_ptr_val:
  rb_step rb_operand_ok m ==>
  rb_step rb_value_ok (\st. as_ptr_val ty loc (m st))
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_as_ptr_val_for))
QED

Theorem rb_compile_type_builtin_dispatch_body:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) ==>
  rb_step rb_value_ok
    (compile_type_builtin_dispatch_body cfn ce vv_ty ty tb ret_ty args)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_type_builtin_dispatch_body_for))
QED

Theorem rb_compile_builtin_dispatch_body:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) ==>
  rb_step rb_value_ok
    (compile_builtin_dispatch_body cfn ce ret_ty ty bi args)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_builtin_dispatch_body_for))
QED

Theorem rb_compile_expr_body:
  rb_env_ok ce /\
  (!env ty e. rb_env_ok env ==> rb_step rb_value_ok (cfn env ty e)) /\
  (!env ret_ty ty bi args. rb_env_ok env ==> rb_step rb_value_ok (bfn env ret_ty ty bi args)) /\
  (!env vv_ty ty tb ret_ty args. rb_env_ok env ==> rb_step rb_value_ok (tfn env vv_ty ty tb ret_ty args)) ==>
  rb_step rb_value_ok (compile_expr_body cfn bfn tfn ce ty e)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_expr_body_for))
QED

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
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_state_ok_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_expr_raw_for))
QED

Theorem compile_expr_no_runtime_begin:
  rb_expr_contract
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_expr_contract_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] compile_expr_label_checks))
QED
