(* Builtin and expression-helper operand exclusion boundaries. *)
Theory runtimeLabelBuiltins
Ancestors
  runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem

Theorem rb_compile_assert_slice_bounds:
  rb_operand_ok sop /\ rb_operand_ok len /\ rb_operand_ok src_len ==>
  rb_step (K T) (compile_assert_slice_bounds sop len src_len)
Proof
  strip_tac >> pure_rewrite_tac[compile_assert_slice_bounds_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_bytestring_src:
  rb_operand_ok src ==>
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (compile_bytestring_src src)
Proof
  strip_tac >> pure_rewrite_tac[compile_bytestring_src_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]
QED

Theorem rb_compile_slice_out_buf:
  !n. rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (compile_slice_out_buf n)
Proof
  gen_tac >> pure_rewrite_tac[compile_slice_out_buf_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]
QED

Theorem rb_compile_slice_data:
  rb_operand_ok src_len /\ rb_operand_ok src_data /\
  rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_data src_len src_data sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_data_def] >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_slice_calldata:
  rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_calldata sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_calldata_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_slice_code:
  rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_code sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_code_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_slice_extcode:
  rb_operand_ok addr /\ rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_extcode addr sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_extcode_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_extract32_load:
  rb_operand_ok src_len /\ rb_operand_ok src_data /\ rb_operand_ok sop ==>
  rb_step rb_operand_ok (compile_extract32_load src_len src_data sop)
Proof
  strip_tac >> pure_rewrite_tac[compile_extract32_load_def] >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED
