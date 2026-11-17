Theory gasShadowCompileBuiltinHash
Ancestors
  gasShadowCompileContext gasShadowState compileEnv builtinHashing

Theorem gas_shadow_compiles_keccak256_word:
  gas_shadow_compiles (compile_keccak256_word val_op) (compile_keccak256_word val_op)
Proof
  simp[compile_keccak256_word_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[]
QED

Theorem gas_shadow_compiles_keccak256_bytes:
  gas_shadow_compiles (compile_keccak256_bytes ptr_op) (compile_keccak256_bytes ptr_op)
Proof
  simp[compile_keccak256_bytes_def, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_keccak256_bytesm:
  gas_shadow_compiles (compile_keccak256_bytesm val_op m) (compile_keccak256_bytesm val_op m)
Proof
  simp[compile_keccak256_bytesm_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[]
QED

Theorem gas_shadow_compiles_sha256_word:
  gas_shadow_compiles (compile_sha256_word val_op) (compile_sha256_word val_op)
Proof
  simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[]
QED

Theorem gas_shadow_compiles_sha256_bytes:
  gas_shadow_compiles (compile_sha256_bytes ptr_op) (compile_sha256_bytes ptr_op)
Proof
  simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[]
QED

Theorem gas_shadow_compiles_sha256_bytesm:
  gas_shadow_compiles (compile_sha256_bytesm val_op m) (compile_sha256_bytesm val_op m)
Proof
  simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[]
QED

Theorem gas_shadow_compiles_method_id_hash:
  gas_shadow_compiles (compile_method_id_hash arg_ty val_op)
    (compile_method_id_hash arg_ty val_op)
Proof
  Cases_on `arg_ty` >> simp[compile_method_id_hash_def,
    gas_shadow_compiles_keccak256_bytes] >>
  rename1 `BaseT base_ty` >> Cases_on `base_ty` >>
  simp[compile_method_id_hash_def, gas_shadow_compiles_keccak256_bytes] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[compile_method_id_hash_def, gas_shadow_compiles_keccak256_bytes,
    gas_shadow_compiles_keccak256_bytesm]
QED

Theorem gas_shadow_compiles_method_id_runtime:
  gas_shadow_compiles (compile_method_id_runtime arg_ty val_op is_bytes4)
    (compile_method_id_runtime arg_ty val_op is_bytes4)
Proof
  Cases_on `is_bytes4` >>
  simp[compile_method_id_runtime_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_method_id_hash, gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_return, gas_shadow_compiles_emit_void] >>
       gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED
