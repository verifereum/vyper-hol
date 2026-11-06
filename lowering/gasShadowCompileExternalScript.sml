(* External-call control boundaries on equal operand inputs. *)
Theory gasShadowCompileExternal
Ancestors
  gasShadowCompileCallSupport gasShadowCompileAbi gasShadowCompileArith
  gasShadowCompileContext gasShadowCompileBase gasShadowState
  exprLowering compileEnv emitHelper venomInst

Theorem gas_shadow_compiles_extcodesize_check:
  gas_shadow_compiles (compile_extcodesize_check addr_op)
    (compile_extcodesize_check addr_op)
Proof
  simp[compile_extcodesize_check_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_return_value_decode:
  gas_shadow_compiles (compile_return_value_decode min_size max_size)
    (compile_return_value_decode min_size max_size)
Proof
  simp[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_select]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_select]
QED

Theorem gas_shadow_compiles_default_return_path:
  gas_shadow_compiles
    (compile_default_return_path cenv return_ty default_ty buf_op result_op
      default_op addr_op skip_check min_size max_size dec_info)
    (compile_default_return_path cenv return_ty default_ty buf_op result_op
      default_op addr_op skip_check min_size max_size dec_info)
Proof
  Cases_on `skip_check` >>
  simp[compile_default_return_path_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block, gas_shadow_compiles_store_memory,
               gas_shadow_compiles_extcodesize_check,
               gas_shadow_compiles_return_value_decode,
               gas_shadow_compiles_abi_decode_to_buf, gas_shadow_compiles_return]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_external_call_kwargs:
  gas_shadow_compiles
    (compile_external_call_kwargs cenv addr_op vals tys mem_size abi_size method_id
      return_size min_size ret_bytes staticcall call_value gas_op skip_check
      has_default default_op return_ty default_ty enc_info dec_info)
    (compile_external_call_kwargs cenv addr_op vals tys mem_size abi_size method_id
      return_size min_size ret_bytes staticcall call_value gas_op skip_check
      has_default default_op return_ty default_ty enc_info dec_info)
Proof
  Cases_on `vals = []` >> Cases_on `return_ty = NoneT` >>
  Cases_on `skip_check` >> Cases_on `staticcall` >> Cases_on `has_default` >>
  simp[compile_external_call_kwargs_def, LET_THM, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> pure_rewrite_tac[comp_bind_assoc] >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_extcall_store_values,
               gas_shadow_compiles_abi_encode_to_buf,
               gas_shadow_compiles_extcodesize_check,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block,
               gas_shadow_compiles_default_return_path,
               gas_shadow_compiles_return_value_decode,
               gas_shadow_compiles_abi_decode_to_buf, gas_shadow_compiles_return]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_default_return_path]
QED
