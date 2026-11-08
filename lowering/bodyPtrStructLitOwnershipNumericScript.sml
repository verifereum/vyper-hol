Theory bodyPtrStructLitOwnershipNumeric
Ancestors bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps builtinSimple builtinMisc builtinMath compileEnv

Theorem alloc_run_compile_builtin_abs:
  alloc_run fresh_outputs (compile_builtin_abs x) (\v s. fresh_outputs s)
Proof
  simp[compile_builtin_abs_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_select]
QED

Theorem alloc_run_compile_blockhash:
  alloc_run fresh_outputs (compile_blockhash x) (\v s. fresh_outputs s)
Proof
  simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_blobhash:
  alloc_run fresh_outputs (compile_blobhash x) (\v s. fresh_outputs s)
Proof
  simp[compile_blobhash_def, SF ETA_ss,
    SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_floor:
  alloc_run fresh_outputs (compile_floor x divisor) (\v s. fresh_outputs s)
Proof
  simp[compile_floor_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_select] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_ceil:
  alloc_run fresh_outputs (compile_ceil x divisor) (\v s. fresh_outputs s)
Proof
  simp[compile_ceil_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_select] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_pow_mod256:
  alloc_run fresh_outputs (compile_pow_mod256 a b) (\v s. fresh_outputs s)
Proof
  simp[compile_pow_mod256_def, SF ETA_ss,
    SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_addmod:
  alloc_run fresh_outputs (compile_addmod a b c) (\v s. fresh_outputs s)
Proof
  simp[compile_addmod_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_mulmod:
  alloc_run fresh_outputs (compile_mulmod a b c) (\v s. fresh_outputs s)
Proof
  simp[compile_mulmod_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED
