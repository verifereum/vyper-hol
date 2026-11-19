(* Builtin and expression-helper operand exclusion boundaries. *)
Theory runtimeLabelBuiltins
Ancestors
  runtimeLabelExprCallbacks runtimeLabelExprPrimitives runtimeLabelBuiltinCore runtimeLabelBuiltinSystem runtimeLabelBuiltinArithmetic
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_powmod256_names_for:
  (rb_env_ok_for source_checks) ce ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_powmod256_names ce ret_ty aty a bty b)
Proof
  strip_tac >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_powmod256_names_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_name_vv_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_unwrap_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_name_vv_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_unwrap_value_for >> simp[]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val_for >>
  simp[rb_compile_pow_mod256_for]
QED

Theorem rb_compile_mod_names_for:
  (rb_env_ok_for source_checks) ce ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_addmod_names ce ret_ty aty a bty b mty m) /\
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_mulmod_names ce ret_ty aty a bty b mty m)
Proof
  strip_tac >> conj_tac >>
  (CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
   pure_rewrite_tac[compile_addmod_names_def, compile_mulmod_names_def, LET_THM] >> BETA_TAC >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_name_vv_for >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_unwrap_value_for >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_name_vv_for >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_unwrap_value_for >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_name_vv_for >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_unwrap_value_for >> simp[]) >>
   gen_tac >> strip_tac >> irule rb_as_stack_val_for >>
   simp[rb_compile_addmod_for, rb_compile_mulmod_for])
QED

Theorem rb_compile_call_raw_revert_for:
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_call cfn ce ret_ty ty RawRevert args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_call_def] >> BETA_TAC
  >- suspend "invalid" >>
  Cases_on `t` >> pure_rewrite_tac[compile_call_def, LET_THM] >> BETA_TAC
  >- suspend "valid" >>
  suspend "invalid"
QED
Resume rb_compile_call_raw_revert_for[invalid]:
  markerLib.RESUME_TAC >>
  (simp[LET_THM] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst_for >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def])
QED
Resume rb_compile_call_raw_revert_for[valid]:
  simp[] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_revert_for >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Finalise rb_compile_call_raw_revert_for

Theorem rb_fresh_vars_for:
  !n. (rb_step_for source_checks) (K T) (fresh_vars n)
Proof
  Induct >> simp[fresh_vars_def, rb_step_return_for] >>
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_fresh_var_for] >>
  gen_tac >> simp[] >> irule rb_step_bind_for >> qexists_tac `K T` >>
  simp[rb_step_return_for]
QED

Theorem rb_emit_multi_op_for:
  EVERY (rb_operand_ok_for source_checks) ops /\ source_codecopy_arity_ok source_checks opc ops ==>
  (rb_step_for source_checks) (EVERY (rb_operand_ok_for source_checks)) (emit_multi_op opc ops n)
Proof
  strip_tac >> pure_rewrite_tac[emit_multi_op_def] >>
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_fresh_vars_for] >> gen_tac >> simp[] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  simp[rb_step_return_for, EVERY_MAP]
QED

Theorem rb_compile_call_internal_for:
  (rb_env_ok_for source_checks) ce /\
  (!e. MEM e (omitted_defaults ce (nsid_to_string id) (LENGTH args)) ==>
    (rb_step_for source_checks) (rb_value_ok_for source_checks)
      (cfn (cenv_without_defaults ce (nsid_to_string id)) (expr_type e) e)) /\
  (!e. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce (expr_type e) e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_call cfn ce ret_ty ty (IntCall id) args default_ret)
Proof
  strip_tac >>
  Cases_on `ce.ce_func_info (nsid_to_string id)` >>
  Cases_on `r` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `OPTION_ALL (rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- suspend "alloc" >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY (rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_stage_intcall_args_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY (rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_stage_intcall_args_for >> simp[rb_env_ok_without_defaults_for]) >>
  gen_tac >> strip_tac >> suspend "invoke"
QED
Resume rb_compile_call_internal_for[alloc]:
  Cases_on `q > 0` >> Cases_on `q' > 0` >> simp[]
  >~ [`(rb_step_for source_checks) _ (\x. (NONE,x))`]
  >- (pure_rewrite_tac[GSYM comp_return_def] >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_step_return_for >> simp[]) >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_alloc_buffer_for) >>
   gen_tac >> strip_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[])
QED
Resume rb_compile_call_internal_for[invoke]:
  Cases_on `return_buf` >> Cases_on `q > 0` >> gvs[]
  >~ [`emit_multi_op _ _ _ _`] >- suspend "multi"
  >~ [`emit_op INVOKE _ _`] >- suspend "single" >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void_for >> gvs[rb_internal_fn_label_for, rb_buffer_ok_for_def]) >>
  gen_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> gvs[rb_value_ok_for_def, rb_base_ptr_for])
QED
Resume rb_compile_call_internal_for[single]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op_for >> simp[rb_internal_fn_label_for]) >>
  gen_tac >> strip_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Resume rb_compile_call_internal_for[multi]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY (rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_multi_op_for >> simp[rb_internal_fn_label_for]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_store_multi_results_for >> gvs[rb_buffer_ok_for_def]) >>
  gen_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def, rb_base_ptr_for]
QED
Finalise rb_compile_call_internal_for

Theorem rb_compile_call_selfdestruct_for:
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_call cfn ce ret_ty ty SelfDestructTarget args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_call_def] >> BETA_TAC
  >- suspend "invalid" >>
  Cases_on `t` >> pure_rewrite_tac[compile_call_def, LET_THM] >> BETA_TAC
  >- suspend "valid" >>
  suspend "invalid"
QED
Resume rb_compile_call_selfdestruct_for[invalid]:
  markerLib.RESUME_TAC >>
  (simp[LET_THM] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst_for >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def])
QED
Resume rb_compile_call_selfdestruct_for[valid]:
  simp[] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_selfdestruct_for >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Finalise rb_compile_call_selfdestruct_for

Theorem rb_compile_call_send_for:
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_call cfn ce ret_ty ty (Send has_gas) args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  Cases_on `t` >> simp[]
  >- suspend "invalid" >>
  Cases_on `LENGTH t' = (if has_gas then 1 else 0)` >> simp[]
  >- suspend "valid" >> suspend "invalid"
QED
Resume rb_compile_call_send_for[invalid]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst_for >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def])
QED
Resume rb_compile_call_send_for[valid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- suspend "gas" >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void_for >> simp[]) >>
  gen_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Resume rb_compile_call_send_for[gas]:
  Cases_on `t'` >> simp[]
  >- (pure_rewrite_tac[GSYM comp_return_def] >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_step_return_for >> simp[]) >>
  Cases_on `t` >> simp[]
  >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_lower_value_for >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[]
QED
Finalise rb_compile_call_send_for

Theorem rb_compile_call_create_for:
  (!dst src info. (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
     (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_to_buf dst src info)) /\
  (rb_env_ok_for source_checks) ce /\
  (!e. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce (expr_type e) e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_call cfn ce ret_ty ty (CreateTarget ck has_salt rof meta) args default_ret)
Proof
  strip_tac >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def] >> irule rb_as_stack_val_for >>
  irule rb_compile_create_call_for >> simp[]
QED

Theorem rb_compile_call_raw_log_for:
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) /\
  (!topics e. MEM topics args /\ MEM e (raw_log_topic_exprs topics) ==>
     (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce (expr_type e) e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_call cfn ce ret_ty ty RawLog args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  Cases_on `t` >> simp[]
  >- suspend "invalid" >>
  Cases_on `t'` >> simp[]
  >- suspend "valid" >> suspend "invalid"
QED
Resume rb_compile_call_raw_log_for[invalid]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst_for >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def])
QED
Resume rb_compile_call_raw_log_for[valid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY (rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_multi_exprs_for >> gvs[]) >>
  gen_tac >> strip_tac >>
  Cases_on `expr_type h' = BaseT (BytesT (Fixed 32))` >> simp[]
  >- suspend "fixed" >> suspend "dynamic"
QED
Resume rb_compile_call_raw_log_for[fixed]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_buffer_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_alloc_buffer_for) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void_for >> gvs[rb_buffer_ok_for_def]) >>
  gen_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_inst_for >> gvs[rb_buffer_ok_for_def, EVERY_MEM, MEM_REVERSE]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Resume rb_compile_call_raw_log_for[dynamic]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op_for >> simp[]) >>
  gen_tac >> strip_tac >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst_for >> gvs[rb_buffer_ok_for_def, EVERY_MEM, MEM_REVERSE]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def])
QED
Finalise rb_compile_call_raw_log_for

Theorem rb_compile_call_raw_calldata_for:
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_call cfn ce ret_ty ty (RawCallCalldataTarget rcf) args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. OPTION_ALL (rb_operand_ok_for source_checks) (FST p) /\
                 OPTION_ALL (rb_operand_ok_for source_checks) (FST (SND p)) /\
                 OPTION_ALL ((rb_operand_ok_for source_checks) o FST) (SND (SND p))`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_kwargs_for >> gvs[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >> simp[] >> strip_tac >> suspend "gas"
QED
Resume rb_compile_call_raw_calldata_for[invalid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_inst_for >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Resume rb_compile_call_raw_calldata_for[gas]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (Cases_on `x1` >> gvs[]
    >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_op_for >> simp[]) >>
    pure_rewrite_tac[GSYM comp_return_def] >>
    CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_step_return_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. (rb_operand_ok_for source_checks) (FST p) /\ (rb_operand_ok_for source_checks) (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_outbuf_for) >>
  PairCases >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. (rb_operand_ok_for source_checks) (FST p) /\ (rb_operand_ok_for source_checks) (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_msg_data_to_memory_for) >>
  PairCases >> simp[] >> strip_tac >> suspend "finish"
QED
Resume rb_compile_call_raw_calldata_for[finish]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_finish_for >> Cases_on `x0` >> gvs[]) >>
  gen_tac >> strip_tac >> Cases_on `rcf.rcf_max_outsize = 0` >> simp[] >>
  (pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def, rb_mk_ptr_for])
QED
Finalise rb_compile_call_raw_calldata_for

Theorem rb_compile_call_raw_for:
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_call cfn ce ret_ty ty (RawCallTarget rcf) args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  Cases_on `t` >> simp[]
  >- suspend "invalid" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. OPTION_ALL (rb_operand_ok_for source_checks) (FST p) /\
                 OPTION_ALL (rb_operand_ok_for source_checks) (FST (SND p)) /\
                 OPTION_ALL ((rb_operand_ok_for source_checks) o FST) (SND (SND p))`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_kwargs_for >> gvs[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >> simp[] >> strip_tac >> suspend "gas"
QED
Resume rb_compile_call_raw_for[invalid]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst_for >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def])
QED
Resume rb_compile_call_raw_for[gas]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (Cases_on `x1` >> gvs[]
    >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_op_for >> simp[]) >>
    pure_rewrite_tac[GSYM comp_return_def] >>
    CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_step_return_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. (rb_operand_ok_for source_checks) (FST p) /\ (rb_operand_ok_for source_checks) (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_outbuf_for) >>
  PairCases >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_finish_for >> Cases_on `x0` >> gvs[]) >>
  gen_tac >> strip_tac >> Cases_on `rcf.rcf_max_outsize = 0` >> simp[] >>
  (pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def, rb_mk_ptr_for])
QED
Finalise rb_compile_call_raw_for

Theorem rb_compile_call_external_for:
  (!dst src info. (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
     (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) hi /\
     (opc = CODECOPY ==> ~SND source_checks) ==>
     (rb_step_for source_checks) (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (rb_env_ok_for source_checks) ce /\
  (!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks)
    (compile_call cfn ce ret_ty ty
      (ExtCall static skip (fname, arg_types, rty) opts) args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY (rb_value_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_args_for >> simp[] >> rpt strip_tac >>
    first_x_assum irule >> simp[] >> drule rich_listTheory.MEM_TAKE >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. OPTION_ALL (rb_operand_ok_for source_checks) (FST p) /\
                 OPTION_ALL (rb_operand_ok_for source_checks) (FST (SND p)) /\
                 OPTION_ALL ((rb_operand_ok_for source_checks) o FST) (SND (SND p))`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_kwargs_for >> simp[] >> rpt strip_tac >>
    first_x_assum irule >> simp[] >> drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >> simp[] >> strip_tac >> suspend "options"
QED
Resume rb_compile_call_external_for[invalid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_inst_for >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return_for >> simp[rb_value_ok_for_def]
QED
Resume rb_compile_call_external_for[options]:
  Cases_on `x2` >> simp[]
  >- suspend "gas" >> PairCases_on `x` >> gvs[] >> suspend "gas"
QED
Resume rb_compile_call_external_for[gas]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (Cases_on `x1` >> gvs[]
    >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_op_for >> simp[]) >>
    pure_rewrite_tac[GSYM comp_return_def] >>
    CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_step_return_for >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `(rb_operand_ok_for source_checks)` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind_for)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_external_call_kwargs_for >>
    simp[rb_every_zip_fst] >> Cases_on `x0` >> gvs[]) >>
  gen_tac >> strip_tac >> Cases_on `rty = NoneT` >> simp[] >>
  (pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return_for >> simp[rb_value_ok_for_def, rb_mk_ptr_for]))
QED
Finalise rb_compile_call_external_for

Theorem rb_compile_call_for:
  (!dst src info. (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
     (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) hi /\
     (opc = CODECOPY ==> ~SND source_checks) ==>
     (rb_step_for source_checks) (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (rb_env_ok_for source_checks) ce /\
  (!id. target = IntCall id ==>
    !e ty. MEM e (omitted_defaults ce (nsid_to_string id) (LENGTH args)) ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn (cenv_without_defaults ce (nsid_to_string id)) ty e)) /\
  (!e ty. expr_size e < list_size expr_size args ==>
     (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)) ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_call cfn ce ret_ty ty target args default_ret)
Proof
  strip_tac >>
  `!e ty. MEM e args ==> (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn ce ty e)` by
    (rpt strip_tac >> first_x_assum irule >>
     drule exprCallBoundsTheory.expr_list_member_bound >> simp[]) >>
  Cases_on `target`
  >- (irule rb_compile_call_internal_for >> simp[])
  >- (PairCases_on `p` >> irule rb_compile_call_external_for >> simp[])
  >- (irule rb_compile_call_send_for >> simp[])
  >- (irule rb_compile_call_raw_for >> simp[])
  >- (irule rb_compile_call_raw_calldata_for >> simp[])
  >- (irule rb_compile_call_raw_log_for >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!e ty. expr_size e < _ ==> _` irule >>
      irule raw_log_topic_exprs_list_member_bound >> metis_tac[])
  >- (irule rb_compile_call_raw_revert_for >> simp[])
  >- (irule rb_compile_call_selfdestruct_for >> simp[]) >>
  irule rb_compile_call_create_for >> simp[]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_compile_powmod256_names:
  rb_env_ok ce ==>
  rb_step rb_value_ok (compile_powmod256_names ce ret_ty aty a bty b)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_powmod256_names_for))
QED

Theorem rb_compile_mod_names:
  rb_env_ok ce ==>
  rb_step rb_value_ok (compile_addmod_names ce ret_ty aty a bty b mty m) /\
  rb_step rb_value_ok (compile_mulmod_names ce ret_ty aty a bty b mty m)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_mod_names_for))
QED

Theorem rb_compile_call_raw_revert:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty RawRevert args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_raw_revert_for))
QED

Theorem rb_fresh_vars:
  !n. rb_step (K T) (fresh_vars n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_fresh_vars_for))
QED

Theorem rb_emit_multi_op:
  EVERY rb_operand_ok ops ==>
  rb_step (EVERY rb_operand_ok) (emit_multi_op opc ops n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_codecopy_arity_ok_def, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_multi_op_for))
QED

Theorem rb_compile_call_internal:
  rb_env_ok ce /\
  (!e. MEM e (omitted_defaults ce (nsid_to_string id) (LENGTH args)) ==>
    rb_step rb_value_ok
      (cfn (cenv_without_defaults ce (nsid_to_string id)) (expr_type e) e)) /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty (IntCall id) args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_internal_for))
QED

Theorem rb_compile_call_selfdestruct:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty SelfDestructTarget args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_selfdestruct_for))
QED

Theorem rb_compile_call_send:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty (Send has_gas) args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_send_for))
QED

Theorem rb_compile_call_create:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty (CreateTarget ck has_salt rof meta) args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_create_for))
QED

Theorem rb_compile_call_raw_log:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) /\
  (!topics e. MEM topics args /\ MEM e (raw_log_topic_exprs topics) ==>
     rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty RawLog args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_raw_log_for))
QED

Theorem rb_compile_call_raw_calldata:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty (RawCallCalldataTarget rcf) args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_raw_calldata_for))
QED

Theorem rb_compile_call_raw:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty (RawCallTarget rcf) args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_raw_for))
QED

Theorem rb_compile_call_external:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty
      (ExtCall static skip (fname, arg_types, rty) opts) args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy, pairTheory.SND,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_external_for))
QED

Theorem rb_compile_call:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_env_ok ce /\
  (!id. target = IntCall id ==>
    !e ty. MEM e (omitted_defaults ce (nsid_to_string id) (LENGTH args)) ==>
      rb_step rb_value_ok (cfn (cenv_without_defaults ce (nsid_to_string id)) ty e)) /\
  (!e ty. expr_size e < list_size expr_size args ==>
     rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty target args default_ret)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy, pairTheory.SND,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_call_for))
QED
