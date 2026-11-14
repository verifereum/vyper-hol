(* Builtin and expression-helper operand exclusion boundaries. *)
Theory runtimeLabelBuiltins
Ancestors
  runtimeLabelExprCallbacks runtimeLabelExprPrimitives runtimeLabelBuiltinCore runtimeLabelBuiltinSystem runtimeLabelBuiltinArithmetic
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_powmod256_names:
  rb_env_ok ce ==>
  rb_step rb_value_ok (compile_powmod256_names ce ret_ty aty a bty b)
Proof
  strip_tac >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_powmod256_names_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_name_vv >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_unwrap_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_name_vv >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_unwrap_value >> simp[]) >>
  gen_tac >> strip_tac >> irule rb_as_stack_val >>
  simp[rb_compile_pow_mod256]
QED

Theorem rb_compile_mod_names:
  rb_env_ok ce ==>
  rb_step rb_value_ok (compile_addmod_names ce ret_ty aty a bty b mty m) /\
  rb_step rb_value_ok (compile_mulmod_names ce ret_ty aty a bty b mty m)
Proof
  strip_tac >> conj_tac >>
  (CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
   pure_rewrite_tac[compile_addmod_names_def, compile_mulmod_names_def, LET_THM] >> BETA_TAC >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_name_vv >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_unwrap_value >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_name_vv >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_unwrap_value >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_name_vv >> simp[]) >>
   gen_tac >> strip_tac >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_unwrap_value >> simp[]) >>
   gen_tac >> strip_tac >> irule rb_as_stack_val >>
   simp[rb_compile_addmod, rb_compile_mulmod])
QED

Theorem rb_compile_call_raw_revert:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty RawRevert args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_call_def] >> BETA_TAC
  >- suspend "invalid" >>
  Cases_on `t` >> pure_rewrite_tac[compile_call_def, LET_THM] >> BETA_TAC
  >- suspend "valid" >>
  suspend "invalid"
QED
Resume rb_compile_call_raw_revert[invalid]:
  markerLib.RESUME_TAC >>
  (simp[LET_THM] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def])
QED
Resume rb_compile_call_raw_revert[valid]:
  simp[] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_revert >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Finalise rb_compile_call_raw_revert

Theorem rb_fresh_vars:
  !n. rb_step (K T) (fresh_vars n)
Proof
  Induct >> simp[fresh_vars_def, rb_step_return] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_fresh_var] >>
  gen_tac >> simp[] >> irule rb_step_bind >> qexists_tac `K T` >>
  simp[rb_step_return]
QED

Theorem rb_emit_multi_op:
  EVERY rb_operand_ok ops ==>
  rb_step (EVERY rb_operand_ok) (emit_multi_op opc ops n)
Proof
  strip_tac >> pure_rewrite_tac[emit_multi_op_def] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_fresh_vars] >> gen_tac >> simp[] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  simp[rb_step_return, EVERY_MAP]
QED

Theorem rb_compile_call_internal:
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty (IntCall id) args default_ret)
Proof
  strip_tac >>
  Cases_on `ce.ce_func_info (nsid_to_string id)` >>
  Cases_on `r` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def] >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `OPTION_ALL rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- suspend "alloc" >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_stage_intcall_args >> simp[]) >>
  gen_tac >> strip_tac >> suspend "invoke"
QED
Resume rb_compile_call_internal[alloc]:
  Cases_on `q > 0` >> Cases_on `q' > 0` >> simp[]
  >~ [`rb_step _ (\x. (NONE,x))`]
  >- (pure_rewrite_tac[GSYM comp_return_def] >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_step_return >> simp[]) >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_compile_alloc_buffer) >>
   gen_tac >> strip_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[])
QED
Resume rb_compile_call_internal[invoke]:
  Cases_on `return_buf` >> Cases_on `q > 0` >> gvs[]
  >~ [`emit_multi_op _ _ _ _`] >- suspend "multi"
  >~ [`emit_op INVOKE _ _`] >- suspend "single" >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void >> gvs[rb_internal_fn_label, rb_buffer_ok_def]) >>
  gen_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> gvs[rb_value_ok_def, rb_base_ptr])
QED
Resume rb_compile_call_internal[single]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op >> simp[rb_internal_fn_label]) >>
  gen_tac >> strip_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Resume rb_compile_call_internal[multi]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_multi_op >> simp[rb_internal_fn_label]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_store_multi_results >> gvs[rb_buffer_ok_def]) >>
  gen_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def, rb_base_ptr]
QED
Finalise rb_compile_call_internal

Theorem rb_compile_call_selfdestruct:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty SelfDestructTarget args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_call_def] >> BETA_TAC
  >- suspend "invalid" >>
  Cases_on `t` >> pure_rewrite_tac[compile_call_def, LET_THM] >> BETA_TAC
  >- suspend "valid" >>
  suspend "invalid"
QED
Resume rb_compile_call_selfdestruct[invalid]:
  markerLib.RESUME_TAC >>
  (simp[LET_THM] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def])
QED
Resume rb_compile_call_selfdestruct[valid]:
  simp[] >> ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_selfdestruct >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Finalise rb_compile_call_selfdestruct

Theorem rb_compile_call_send:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty (Send has_gas) args default_ret)
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
Resume rb_compile_call_send[invalid]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def])
QED
Resume rb_compile_call_send[valid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- suspend "gas" >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void >> simp[]) >>
  gen_tac >> pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Resume rb_compile_call_send[gas]:
  Cases_on `t'` >> simp[]
  >- (pure_rewrite_tac[GSYM comp_return_def] >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_step_return >> simp[]) >>
  Cases_on `t` >> simp[]
  >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_lower_value >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[]
QED
Finalise rb_compile_call_send

Theorem rb_compile_call_create:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty (CreateTarget ck has_salt rof meta) args default_ret)
Proof
  strip_tac >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def] >> irule rb_as_stack_val >>
  irule rb_compile_create_call >> simp[]
QED

Theorem rb_compile_call_raw_log:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) /\
  (!topics e. MEM topics args /\ MEM e (raw_log_topic_exprs topics) ==>
     rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty RawLog args default_ret)
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
Resume rb_compile_call_raw_log[invalid]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def])
QED
Resume rb_compile_call_raw_log[valid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_multi_exprs >> gvs[]) >>
  gen_tac >> strip_tac >>
  Cases_on `expr_type h' = BaseT (BytesT (Fixed 32))` >> simp[]
  >- suspend "fixed" >> suspend "dynamic"
QED
Resume rb_compile_call_raw_log[fixed]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_buffer_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_alloc_buffer) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void >> gvs[rb_buffer_ok_def]) >>
  gen_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_inst >> gvs[rb_buffer_ok_def, EVERY_MEM, MEM_REVERSE]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Resume rb_compile_call_raw_log[dynamic]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op >> simp[]) >>
  gen_tac >> strip_tac >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst >> gvs[rb_buffer_ok_def, EVERY_MEM, MEM_REVERSE]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def])
QED
Finalise rb_compile_call_raw_log

Theorem rb_compile_call_raw_calldata:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty (RawCallCalldataTarget rcf) args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. OPTION_ALL rb_operand_ok (FST p) /\
                 OPTION_ALL rb_operand_ok (FST (SND p)) /\
                 OPTION_ALL (rb_operand_ok o FST) (SND (SND p))`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_kwargs >> gvs[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >> simp[] >> strip_tac >> suspend "gas"
QED
Resume rb_compile_call_raw_calldata[invalid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_inst >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Resume rb_compile_call_raw_calldata[gas]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (Cases_on `x1` >> gvs[]
    >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_op >> simp[]) >>
    pure_rewrite_tac[GSYM comp_return_def] >>
    CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_step_return >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_outbuf) >>
  PairCases >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_msg_data_to_memory) >>
  PairCases >> simp[] >> strip_tac >> suspend "finish"
QED
Resume rb_compile_call_raw_calldata[finish]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_finish >> Cases_on `x0` >> gvs[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_void >> simp[]) >>
  gen_tac >> Cases_on `rcf.rcf_max_outsize = 0` >> simp[] >>
  (pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def, rb_mk_ptr])
QED
Finalise rb_compile_call_raw_calldata

Theorem rb_compile_call_raw:
  rb_env_ok ce /\
  (!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok
    (compile_call cfn ce ret_ty ty (RawCallTarget rcf) args default_ret)
Proof
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  Cases_on `t` >> simp[]
  >- suspend "invalid" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_op >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. OPTION_ALL rb_operand_ok (FST p) /\
                 OPTION_ALL rb_operand_ok (FST (SND p)) /\
                 OPTION_ALL (rb_operand_ok o FST) (SND (SND p))`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_kwargs >> gvs[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >> simp[] >> strip_tac >> suspend "gas"
QED
Resume rb_compile_call_raw[invalid]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
     (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_emit_inst >> simp[]) >>
   pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def])
QED
Resume rb_compile_call_raw[gas]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (Cases_on `x1` >> gvs[]
    >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_op >> simp[]) >>
    pure_rewrite_tac[GSYM comp_return_def] >>
    CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_step_return >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_outbuf) >>
  PairCases >> simp[] >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_raw_call_finish >> Cases_on `x0` >> gvs[]) >>
  gen_tac >> strip_tac >> Cases_on `rcf.rcf_max_outsize = 0` >> simp[] >>
  (pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def, rb_mk_ptr])
QED
Finalise rb_compile_call_raw

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
  strip_tac >> Cases_on `args` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  simp[compile_call_def]
  >- suspend "invalid" >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `EVERY rb_value_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_args >> simp[] >> rpt strip_tac >>
    first_x_assum irule >> simp[] >> drule rich_listTheory.MEM_TAKE >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `\p. OPTION_ALL rb_operand_ok (FST p) /\
                 OPTION_ALL rb_operand_ok (FST (SND p)) /\
                 OPTION_ALL (rb_operand_ok o FST) (SND (SND p))`
      (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_ext_call_kwargs >> simp[] >> rpt strip_tac >>
    first_x_assum irule >> simp[] >> drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >> simp[] >> strip_tac >> suspend "options"
QED
Resume rb_compile_call_external[invalid]:
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_emit_inst >> simp[]) >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
  irule rb_step_return >> simp[rb_value_ok_def]
QED
Resume rb_compile_call_external[options]:
  Cases_on `x2` >> simp[]
  >- suspend "gas" >> PairCases_on `x` >> gvs[] >> suspend "gas"
QED
Resume rb_compile_call_external[gas]:
  markerLib.RESUME_TAC >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (Cases_on `x1` >> gvs[]
    >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_op >> simp[]) >>
    pure_rewrite_tac[GSYM comp_return_def] >>
    CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_step_return >> simp[]) >>
  gen_tac >> strip_tac >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
  conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
    irule rb_compile_external_call_kwargs >>
    simp[rb_every_zip_fst] >> Cases_on `x0` >> gvs[]) >>
  gen_tac >> strip_tac >> Cases_on `rty = NoneT` >> simp[] >>
  (pure_rewrite_tac[GSYM comp_return_def] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_step_return >> simp[rb_value_ok_def, rb_mk_ptr]))
QED
Finalise rb_compile_call_external

Theorem rb_compile_call:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_env_ok ce /\
  (!e ty. expr_size e < list_size expr_size args ==>
     rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step rb_value_ok (compile_call cfn ce ret_ty ty target args default_ret)
Proof
  strip_tac >>
  `!e ty. MEM e args ==> rb_step rb_value_ok (cfn ce ty e)` by
    (rpt strip_tac >> first_x_assum irule >>
     drule exprCallBoundsTheory.expr_list_member_bound >> simp[]) >>
  Cases_on `target`
  >- (irule rb_compile_call_internal >> simp[])
  >- (PairCases_on `p` >> irule rb_compile_call_external >> simp[])
  >- (irule rb_compile_call_send >> simp[])
  >- (irule rb_compile_call_raw >> simp[])
  >- (irule rb_compile_call_raw_calldata >> simp[])
  >- (irule rb_compile_call_raw_log >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!e ty. expr_size e < _ ==> _` irule >>
      irule raw_log_topic_exprs_list_member_bound >> metis_tac[])
  >- (irule rb_compile_call_raw_revert >> simp[])
  >- (irule rb_compile_call_selfdestruct >> simp[]) >>
  irule rb_compile_call_create >> simp[]
QED
