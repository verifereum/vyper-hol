Theory gasShadowCompileBuiltinBytes
Ancestors
  gasShadowCompileContext gasShadowState compileEnv builtinBytes

Theorem gas_shadow_compiles_assert_slice_bounds:
  gas_shadow_compiles (compile_assert_slice_bounds start_op length_op src_len_op)
    (compile_assert_slice_bounds start_op length_op src_len_op)
Proof
  simp[compile_assert_slice_bounds_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_bytestring_src:
  gas_shadow_compiles (compile_bytestring_src src_ptr) (compile_bytestring_src src_ptr)
Proof
  simp[compile_bytestring_src_def, gas_shadow_compiles_bind, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_slice_out_buf:
  gas_shadow_compiles (compile_slice_out_buf out_size) (compile_slice_out_buf out_size)
Proof
  simp[compile_slice_out_buf_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_slice_data:
  gas_shadow_compiles (compile_slice_data src_len src_data start_op length_op out_size)
    (compile_slice_data src_len src_data start_op length_op out_size)
Proof
  simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_assert_slice_bounds, gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_return, gas_shadow_compiles_emit_void] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_slice_extcode:
  gas_shadow_compiles (compile_slice_extcode addr_op start_op length_op out_buf out_data)
    (compile_slice_extcode addr_op start_op length_op out_buf out_data)
Proof
  simp[compile_slice_extcode_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_assert_slice_bounds, gas_shadow_compiles_emit_void] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_extract32_load:
  gas_shadow_compiles (compile_extract32_load src_len src_data start_op)
    (compile_extract32_load src_len src_data start_op)
Proof
  simp[compile_extract32_load_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_assert_slice_bounds] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_slice_calldata:
  gas_shadow_compiles (compile_slice_calldata start_op length_op out_size)
    (compile_slice_calldata start_op length_op out_size)
Proof
  simp[compile_slice_calldata_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_slice_out_buf] >>
  gen_tac >> pairarg_tac >> gvs[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_assert_slice_bounds, gas_shadow_compiles_emit_void] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_slice_code:
  gas_shadow_compiles (compile_slice_code start_op length_op out_size)
    (compile_slice_code start_op length_op out_size)
Proof
  simp[compile_slice_code_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_slice_out_buf] >>
  gen_tac >> pairarg_tac >> gvs[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_assert_slice_bounds, gas_shadow_compiles_emit_void] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED
