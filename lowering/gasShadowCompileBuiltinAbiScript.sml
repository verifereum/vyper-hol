Theory gasShadowCompileBuiltinAbi
Ancestors
  gasShadowCompileAbi gasShadowCompileContext gasShadowState compileEnv
  builtinAbi exprLowering

Theorem gas_shadow_compiles_lower_abi_encode:
  gas_shadow_compiles (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
    (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
Proof
  Cases_on `method_id_opt` >>
  simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_op, gas_shadow_compiles_bind,
               gas_shadow_compiles_abi_encode_to_buf] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_lower_abi_decode:
  gas_shadow_compiles (lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size)
    (lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size)
Proof
  Cases_on `abi_min_size = abi_max_size` >> (
  simp[lower_abi_decode_def, comp_ignore_bind_def] >>
  ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
          >- simp[] >> gen_tac >> BETA_TAC) >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- simp[] >> gen_tac >> BETA_TAC) >>
      simp[gas_shadow_compiles_emit_void]) >>
  gen_tac >> BETA_TAC >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_abi_decode_to_buf] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_store_abi_tuple:
  !entries off.
    gas_shadow_compiles (compile_store_abi_tuple cenv buf off entries)
      (compile_store_abi_tuple cenv buf off entries)
Proof
  Induct_on `entries` >- simp[compile_store_abi_tuple_def, gas_shadow_compiles_return] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_copy_memory]) >>
  simp[]
QED
