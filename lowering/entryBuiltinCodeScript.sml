Theory entryBuiltinCode
Ancestors
  entryAggregateCode entryArithmeticCode entryValueCode entryLocationValueCode
  builtinMath builtinMisc builtinSimple
  exprLowering entryCodePredicate entryContextCodePredicate builtinBytes builtinStrings

Theorem entry_code_invert:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_invert v ty cenv)
Proof
  Cases_on `ty` >> simp[compile_invert_def, entry_code_emit_op]
QED

Theorem entry_code_neg:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_neg v ty)
Proof
  simp[compile_neg_def] >> pairarg_tac >>
  simp[compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_pow_mod256:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_pow_mod256 v w)
Proof
  simp[compile_pow_mod256_def, entry_code_emit_op]
QED

Theorem entry_code_addmod:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_addmod a b c)
Proof
  simp[compile_addmod_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_void, entry_code_emit_op]
QED

Theorem entry_code_mulmod:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_mulmod a b c)
Proof
  simp[compile_mulmod_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_void, entry_code_emit_op]
QED

Theorem entry_code_builtin_abs:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_builtin_abs v)
Proof
  simp[compile_builtin_abs_def, compile_select_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_blockhash:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_blockhash v)
Proof
  simp[compile_blockhash_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_blobhash:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_blobhash v)
Proof
  simp[compile_blobhash_def, entry_code_emit_op]
QED

Theorem entry_code_as_wei_value_int:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_as_wei_value_int v scale signed)
Proof
  `!a. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (do p <- emit_op SLT [v; Lit 0w];
         n <- emit_op ISZERO [p]; emit_op AND [n; a] od)` by
    (gen_tac >> rpt (irule entry_code_bind >> reverse conj_tac
      >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
     simp[entry_code_emit_op]) >>
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void, entry_code_return] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_as_wei_value_decimal:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_as_wei_value_decimal v scale divisor)
Proof
  Cases_on `scale = 1` >>
  simp[compile_as_wei_value_decimal_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_ecrecover:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_ecrecover h v r s)
Proof
  simp[compile_ecrecover_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return,
            entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_ecadd_points:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_ecadd_points p1 p2)
Proof
  simp[compile_ecadd_points_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return,
            entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_ecmul_point:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_ecmul_point p scalar)
Proof
  simp[compile_ecmul_point_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return,
            entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_zero_words[local]:
  !n. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_zero_words buf n)
Proof
  Induct >> simp[compile_zero_words_def, entry_code_return,
                 compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_emit_op, entry_code_emit_void]
QED

Theorem entry_code_builtin_empty_complex:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_empty_complex sz bs)
Proof
  simp[compile_builtin_empty_complex_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_alloc_buffer] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_return] >> rpt gen_tac >> BETA_TAC >>
  Cases_on `bs` >> simp[] >> irule entry_code_bind >>
  simp[entry_code_emit_void, entry_code_zero_words, entry_code_return]
QED

Theorem entry_code_assert_slice_bounds[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_assert_slice_bounds start len src)
Proof
  simp[compile_assert_slice_bounds_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_slice_out_buf[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_slice_out_buf sz)
Proof
  simp[compile_slice_out_buf_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_op, entry_code_return] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_slice_calldata:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_slice_calldata start len sz)
Proof
  simp[compile_slice_calldata_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_assert_slice_bounds, entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_uint2str:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_uint2str v nd sz)
Proof
  simp[compile_uint2str_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return, entry_code_emit_inst,
            entry_code_emit_op, entry_code_emit_void, entry_code_fresh_var,
            entry_code_fresh_label, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_addmod_names:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_addmod_names cenv ret_ty aty a bty b mty m)
Proof
  rw[entry_preserves_code_def, compile_addmod_names_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `compile_addmod va vb vm st6` >> gvs[as_stack_val_def] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_name_vv) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_unwrap_value) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_addmod) >>
  metis_tac[]
QED

Theorem entry_code_mulmod_names:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_mulmod_names cenv ret_ty aty a bty b mty m)
Proof
  rw[entry_preserves_code_def, compile_mulmod_names_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `compile_mulmod va vb vm st6` >> gvs[as_stack_val_def] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_name_vv) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_unwrap_value) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_mulmod) >>
  metis_tac[]
QED

Theorem entry_code_powmod256_names:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_powmod256_names cenv ret_ty aty a bty b)
Proof
  rw[entry_preserves_code_def, compile_powmod256_names_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `compile_pow_mod256 va vb st4` >> gvs[as_stack_val_def] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_name_vv) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_unwrap_value) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_pow_mod256) >>
  metis_tac[]
QED
