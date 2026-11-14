(* Builtin and expression-helper operand exclusion boundaries. *)
Theory runtimeLabelBuiltins
Ancestors
  runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering

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

Theorem rb_compile_select:
  rb_operand_ok c /\ rb_operand_ok a /\ rb_operand_ok b ==>
  rb_step rb_operand_ok (compile_select c a b)
Proof
  strip_tac >> pure_rewrite_tac[compile_select_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_builtin_len:
  !ptr ctor imm loc. rb_operand_ok ptr /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step rb_operand_ok (compile_builtin_len ctor imm ptr loc)
Proof
  simp[compile_builtin_len_def, rb_compile_ptr_load]
QED

Theorem rb_compile_builtin_calldatasize:
  rb_step rb_operand_ok compile_builtin_calldatasize
Proof
  simp[compile_builtin_calldatasize_def, rb_emit_op]
QED

Theorem rb_compile_builtin_empty_prim:
  rb_step rb_operand_ok compile_builtin_empty_prim
Proof
  simp[compile_builtin_empty_prim_def, rb_step_return]
QED

Theorem rb_compile_zero_words:
  !n base_op. rb_operand_ok base_op ==>
  rb_step (K T) (compile_zero_words base_op n)
Proof
  Induct >> rpt strip_tac >> pure_rewrite_tac[compile_zero_words_def]
  >- simp[rb_step_return] >>
  irule rb_ignore >> conj_tac >- simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_builtin_empty_complex:
  !n bytes. rb_step rb_buffer_ok (compile_builtin_empty_complex n bytes)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_builtin_empty_complex_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> strip_tac >> irule rb_bind_return >> BETA_TAC >>
  Cases_on `bytes` >> simp[LET_THM] >>
  irule rb_ignore >> simp[rb_emit_void, rb_compile_zero_words,
                            rb_step_return, rb_buffer_ok_def] >>
  gvs[rb_buffer_ok_def, rb_emit_void, rb_compile_zero_words]
QED

Theorem rb_compile_builtin_min:
  rb_operand_ok a /\ rb_operand_ok b ==>
  rb_step rb_operand_ok (compile_builtin_min a b unsigned)
Proof
  strip_tac >> pure_rewrite_tac[compile_builtin_min_def] >>
  Cases_on `unsigned` >> simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_select]
QED

Theorem rb_compile_builtin_max:
  rb_operand_ok a /\ rb_operand_ok b ==>
  rb_step rb_operand_ok (compile_builtin_max a b unsigned)
Proof
  strip_tac >> pure_rewrite_tac[compile_builtin_max_def] >>
  Cases_on `unsigned` >> simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_select]
QED

Theorem rb_compile_builtin_abs:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_builtin_abs v)
Proof
  strip_tac >> pure_rewrite_tac[compile_builtin_abs_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_compile_select]
QED

Theorem rb_compile_msg_data_to_memory:
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    compile_msg_data_to_memory
Proof
  pure_rewrite_tac[compile_msg_data_to_memory_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_dynamic] >>
  gen_tac >> strip_tac >> irule rb_ignore >>
  simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_raw_call_outbuf:
  !n. rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (compile_raw_call_outbuf n)
Proof
  gen_tac >> pure_rewrite_tac[compile_raw_call_outbuf_def] >>
  Cases_on `n > 0` >> simp[LET_THM]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_bind_return >> BETA_TAC >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  simp[rb_buffer_ok_def, rb_step_return]
QED

Theorem rb_compile_send:
  rb_operand_ok to_op /\ rb_operand_ok value_op /\ rb_operand_ok gas_op ==>
  rb_step (K T) (compile_send to_op value_op gas_op)
Proof
  strip_tac >> pure_rewrite_tac[compile_send_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_raw_revert:
  rb_operand_ok data_ptr ==> rb_step (K T) (compile_raw_revert data_ptr)
Proof
  strip_tac >> pure_rewrite_tac[compile_raw_revert_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_inst]
QED

Theorem rb_compile_selfdestruct:
  rb_operand_ok to_op ==> rb_step (K T) (compile_selfdestruct to_op)
Proof
  simp[compile_selfdestruct_def, rb_emit_void]
QED

Theorem rb_compile_raw_call_finish:
  rb_operand_ok to_op /\ rb_operand_ok data_ptr /\ rb_operand_ok data_len /\
  rb_operand_ok gas_op /\ rb_operand_ok value_op /\
  rb_operand_ok out_val /\ rb_operand_ok out_ptr ==>
  rb_step rb_operand_ok
    (compile_raw_call_finish to_op data_ptr data_len gas_op value_op
      call_ty max_outsize revert_on_failure out_val out_ptr)
Proof
  strip_tac >> pure_rewrite_tac[compile_raw_call_finish_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `call_ty` >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >> Cases_on `revert_on_failure` >> simp[]
  >- suspend "revert" >> suspend "no_revert"
QED

Resume rb_compile_raw_call_finish[revert]:
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  Cases_on `max_outsize > 0` >> simp[rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select] >>
  gen_tac >> strip_tac >> irule rb_ignore >>
  simp[rb_emit_void, rb_step_return]
QED

Resume rb_compile_raw_call_finish[no_revert]:
  Cases_on `max_outsize > 0` >> simp[LET_THM, rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select] >>
  gen_tac >> strip_tac >> irule rb_ignore >>
  conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Finalise rb_compile_raw_call_finish

Theorem rb_compile_unsafe_binop:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_unsafe_binop opc x y bits signed)
Proof
  strip_tac >> pure_rewrite_tac[compile_unsafe_binop_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `bits < 256` >> Cases_on `signed` >>
  simp[LET_THM, rb_emit_op, rb_step_return]
QED

Theorem rb_compile_unsafe_add:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_unsafe_add x y bits signed)
Proof simp[compile_unsafe_add_def, rb_compile_unsafe_binop]
QED

Theorem rb_compile_unsafe_sub:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_unsafe_sub x y bits signed)
Proof simp[compile_unsafe_sub_def, rb_compile_unsafe_binop]
QED

Theorem rb_compile_unsafe_mul:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_unsafe_mul x y bits signed)
Proof simp[compile_unsafe_mul_def, rb_compile_unsafe_binop]
QED

Theorem rb_compile_unsafe_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_unsafe_div x y bits signed)
Proof simp[compile_unsafe_div_def, rb_compile_unsafe_binop]
QED

Theorem rb_compile_pow_mod256:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_pow_mod256 x y)
Proof simp[compile_pow_mod256_def, rb_emit_op]
QED

Theorem rb_compile_addmod:
  rb_operand_ok a /\ rb_operand_ok b /\ rb_operand_ok c ==>
  rb_step rb_operand_ok (compile_addmod a b c)
Proof
  strip_tac >> pure_rewrite_tac[compile_addmod_def] >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_mulmod:
  rb_operand_ok a /\ rb_operand_ok b /\ rb_operand_ok c ==>
  rb_step rb_operand_ok (compile_mulmod a b c)
Proof
  strip_tac >> pure_rewrite_tac[compile_mulmod_def] >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_shift:
  rb_operand_ok v /\ rb_operand_ok bits_op ==>
  rb_step rb_operand_ok (compile_shift v bits_op signed)
Proof
  strip_tac >> pure_rewrite_tac[compile_shift_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `signed` >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_compile_select]
QED

Theorem rb_compile_keccak256_word:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_keccak256_word v)
Proof
  strip_tac >> pure_rewrite_tac[compile_keccak256_word_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_keccak256_bytes:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_keccak256_bytes p)
Proof
  strip_tac >> pure_rewrite_tac[compile_keccak256_bytes_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_keccak256_bytesm:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_keccak256_bytesm v n)
Proof
  strip_tac >> pure_rewrite_tac[compile_keccak256_bytesm_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_method_id_hash:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_method_id_hash ty v)
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def, rb_compile_keccak256_bytes] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, rb_compile_keccak256_bytes] >>
  rename1 `BytesT len` >> Cases_on `len` >>
  simp[compile_method_id_hash_def, rb_compile_keccak256_bytes,
       rb_compile_keccak256_bytesm]
QED

Theorem rb_compile_method_id_runtime:
  rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_method_id_runtime ty v bytes4)
Proof
  strip_tac >> pure_rewrite_tac[compile_method_id_runtime_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_method_id_hash] >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `bytes4` >> simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_sha256_word:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_sha256_word v)
Proof
  strip_tac >> pure_rewrite_tac[compile_sha256_word_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_sha256_bytes:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_sha256_bytes p)
Proof
  strip_tac >> pure_rewrite_tac[compile_sha256_bytes_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_sha256_bytesm:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_sha256_bytesm v n)
Proof
  strip_tac >> pure_rewrite_tac[compile_sha256_bytesm_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_uint2str:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_uint2str v digits nbytes)
Proof
  strip_tac >> pure_rewrite_tac[compile_uint2str_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  suspend "body"
QED

Resume rb_compile_uint2str[body]:
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> simp[rb_new_block, rb_step_return]
QED

Finalise rb_compile_uint2str

Theorem rb_compile_ecrecover:
  rb_operand_ok h /\ rb_operand_ok v /\ rb_operand_ok r /\ rb_operand_ok s ==>
  rb_step rb_operand_ok (compile_ecrecover h v r s)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecrecover_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_ecadd:
  rb_operand_ok x1 /\ rb_operand_ok y1 /\ rb_operand_ok x2 /\ rb_operand_ok y2 ==>
  rb_step rb_operand_ok (compile_ecadd x1 y1 x2 y2)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecadd_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_ecmul:
  rb_operand_ok x /\ rb_operand_ok y /\ rb_operand_ok scalar ==>
  rb_step rb_operand_ok (compile_ecmul x y scalar)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecmul_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_ecadd_points:
  rb_operand_ok p1 /\ rb_operand_ok p2 ==>
  rb_step rb_operand_ok (compile_ecadd_points p1 p2)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecadd_points_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_ecmul_point:
  rb_operand_ok p /\ rb_operand_ok scalar ==>
  rb_step rb_operand_ok (compile_ecmul_point p scalar)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecmul_point_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_blockhash:
  rb_operand_ok n ==> rb_step rb_operand_ok (compile_blockhash n)
Proof
  strip_tac >> pure_rewrite_tac[compile_blockhash_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_blobhash:
  rb_operand_ok n ==> rb_step rb_operand_ok (compile_blobhash n)
Proof
  simp[compile_blobhash_def, rb_emit_op]
QED

Theorem rb_compile_floor:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_floor v divisor)
Proof
  strip_tac >> pure_rewrite_tac[compile_floor_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select] >>
  simp[rb_emit_op]
QED

Theorem rb_compile_ceil:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_ceil v divisor)
Proof
  strip_tac >> pure_rewrite_tac[compile_ceil_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select] >>
  simp[rb_emit_op]
QED

Theorem rb_compile_as_wei_value_int:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_as_wei_value_int v scale signed)
Proof
  strip_tac >> pure_rewrite_tac[compile_as_wei_value_int_def] >>
  Cases_on `scale = 1` >> simp[rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `signed` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >> irule rb_ignore >>
  simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_as_wei_value_decimal:
  rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_as_wei_value_decimal v scale divisor)
Proof
  strip_tac >> pure_rewrite_tac[compile_as_wei_value_decimal_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  Cases_on `scale = 1` >> simp[rb_emit_op] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

(* The encoder antecedent is conjunct 2 of runtimeLabelABI$rb_abi_encode. *)
Theorem rb_lower_abi_encode:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_operand_ok src_op ==>
  rb_step rb_operand_ok (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
Proof
  strip_tac >> pure_rewrite_tac[lower_abi_encode_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `method_id_opt` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >>
  gen_tac >> strip_tac >> irule rb_ignore >> reverse conj_tac
  >- simp[rb_step_return] >>
  Cases_on `(case method_id_opt of SOME _ => 4 | NONE => 0) > 0` >>
  simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

(* The decoder antecedent is conjunct 1 of runtimeLabelABI$rb_abi_decode. *)
Theorem rb_lower_abi_decode:
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_operand_ok data_op ==>
  rb_step rb_operand_ok (lower_abi_decode data_op dec_info min_size max_size out_size)
Proof
  strip_tac >> pure_rewrite_tac[lower_abi_decode_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `min_size = max_size` >> simp[]
      >- (irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> simp[rb_step_return]
QED

Theorem rb_compile_check_create_result:
  rb_operand_ok result ==>
  rb_step rb_operand_ok (compile_check_create_result result revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_check_create_result_def] >>
  Cases_on `revert_on_failure` >> simp[rb_step_return] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> simp[rb_new_block, rb_step_return]
QED

Theorem rb_compile_create_dispatch:
  rb_operand_ok code_ptr /\ rb_operand_ok code_len /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) ==>
  rb_step rb_operand_ok
    (compile_create_dispatch code_ptr code_len value_op salt_opt revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_dispatch_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `salt_opt` >> gvs[rb_emit_op]) >>
  simp[rb_compile_check_create_result]
QED

Theorem rb_compile_create_proxy_buf:
  rb_operand_ok target ==>
  rb_step rb_operand_ok (compile_create_proxy_buf target)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_proxy_buf_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_create_proxy:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) ==>
  rb_step rb_operand_ok (compile_create_proxy target value_op salt_opt revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_proxy_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_proxy_buf] >>
  simp[rb_compile_create_dispatch]
QED

Theorem rb_compile_create_copy:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) ==>
  rb_step rb_operand_ok (compile_create_copy target value_op salt_opt revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_copy_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_dynamic] >>
  gen_tac >> strip_tac >> irule rb_ignore >>
  conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `salt_opt` >> gvs[rb_emit_op]) >>
  simp[rb_compile_check_create_result]
QED

Theorem rb_compile_create_blueprint_check:
  rb_operand_ok target /\ rb_operand_ok offset ==>
  rb_step rb_operand_ok (compile_create_blueprint_check target offset)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_check_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_create_blueprint_append:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) /\
  rb_operand_ok offset /\ rb_operand_ok code_size /\
  rb_operand_ok args_ptr /\ rb_operand_ok args_len ==>
  rb_step rb_operand_ok
    (compile_create_blueprint_append target value_op salt_opt offset
      code_size args_ptr args_len revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_append_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_dynamic] >>
  gen_tac >> strip_tac >> irule rb_ignore >>
  conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `args_len = Lit 0w` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_copy_memory_dynamic]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `salt_opt` >> gvs[rb_emit_op]) >>
  simp[rb_compile_check_create_result]
QED

Theorem rb_compile_create_blueprint:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) /\
  rb_operand_ok offset /\
  (case args_info of NONE => T | SOME (p,n) => rb_operand_ok p /\ rb_operand_ok n) ==>
  rb_step rb_operand_ok
    (compile_create_blueprint target value_op salt_opt offset args_info revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_blueprint_check] >>
  gen_tac >> strip_tac >> Cases_on `args_info` >>
  gvs[LET_THM, rb_compile_create_blueprint_append] >>
  PairCases_on `x'` >> gvs[rb_compile_create_blueprint_append]
QED

Theorem rb_compile_clamp:
  rb_operand_ok v ==> rb_step (K T) (compile_clamp v ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_clamp_def, LET_THM] >>
  pairarg_tac >> BETA_TAC >> Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_clamp_and_return:
  rb_operand_ok v ==> rb_step rb_operand_ok (clamp_and_return v ty)
Proof
  strip_tac >> pure_rewrite_tac[clamp_and_return_def] >>
  irule rb_ignore >> simp[rb_compile_clamp, rb_step_return]
QED

Theorem rb_compile_clamp_basetype:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, rb_step_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, rb_step_return] >> strip_tac
  >- (Cases_on `n < 256` >> simp[rb_clamp_and_return, rb_step_return])
  >- (Cases_on `n < 256` >> simp[rb_clamp_and_return, rb_step_return])
  >- (rename1 `BytesT len` >> Cases_on `len` >>
      simp[compile_clamp_basetype_def, rb_step_return] >>
      rename1 `m < 32` >> Cases_on `m < 32` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_safe_add:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_add x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_add_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_safe_sub:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_sub x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_sub_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_mul_overflow_check:
  rb_operand_ok x /\ rb_operand_ok y /\ rb_operand_ok res ==>
  rb_step (K T) (compile_mul_overflow_check x y res signed bits)
Proof
  strip_tac >> pure_rewrite_tac[compile_mul_overflow_check_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `signed /\ bits = 256` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]) >>
  simp[rb_emit_void]
QED

Theorem rb_compile_safe_mul:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_mul x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_mul_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `type_bits ty > 128` >>
      simp[rb_compile_mul_overflow_check, rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `is_decimal_type ty` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >> Cases_on `type_bits ty < 256 \/ is_decimal_type ty` >>
  simp[rb_clamp_and_return, rb_step_return]
QED

Theorem rb_compile_safe_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_div x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_div_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  Cases_on `is_signed_type ty` >> simp[rb_emit_op] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty = 256` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return, rb_step_return]
QED

Theorem rb_compile_safe_decimal_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_decimal_div x y divisor ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_decimal_div_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_clamp_and_return]
QED

Theorem rb_compile_safe_mod:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_mod x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_mod_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  Cases_on `is_signed_type ty` >> simp[rb_emit_op]
QED

Theorem rb_compile_safe_pow:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_pow x y ty bl el)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_pow_def, LET_THM] >> BETA_TAC >>
  Cases_on `bl` >> simp[]
  >- suspend "exponent" >>
  rename1 `bi = -1` >> Cases_on `bi = -1 \/ bi = 0 \/ bi = 1` >> simp[LET_THM]
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac
      >- (Cases_on `is_signed_type ty` >> simp[rb_step_return] >>
          irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> irule rb_ignore >> simp[rb_emit_void, rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Resume rb_compile_safe_pow[exponent]:
  Cases_on `el` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_compile_clamp, rb_step_return]) >>
  rename1 `Num ei = 1` >> Cases_on `ei = 0 \/ Num ei = 1` >> simp[LET_THM]
  >- (irule rb_ignore >> simp[rb_emit_void, rb_emit_op]) >>
  Cases_on `is_signed_type ty` >> simp[LET_THM]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Finalise rb_compile_safe_pow

Theorem rb_wrap_truncate:
  rb_operand_ok v ==> rb_step rb_operand_ok (wrap_truncate v ty)
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, rb_emit_op, rb_step_return]
QED

Theorem rb_compile_compare:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_compare op x y ty)
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, rb_emit_op, LET_THM]
  >> FIRST_PROVE
     [irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op],
      irule rb_ignore >> simp[rb_emit_inst, rb_step_return]]
QED

Theorem rb_compile_binop:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_binop op x y ty bl el)
Proof
  strip_tac >> Cases_on `op` >>
  simp[compile_binop_def, rb_compile_safe_add, rb_compile_safe_sub,
       rb_compile_safe_mul, rb_compile_safe_mod, rb_compile_safe_pow,
       rb_compile_compare, rb_emit_op, LET_THM]
  >>~- ([`if is_decimal_type ty then _ else _`],
        Cases_on `is_decimal_type ty` >> simp[rb_compile_safe_decimal_div, rb_compile_safe_div])
  >>~- ([`if is_signed_type ty then emit_op _ _ else _`],
        Cases_on `is_signed_type ty` >> simp[rb_emit_op])
  >>~- ([`comp_bind (emit_op _ _) (\res. wrap_truncate res ty)`],
        irule rb_bind_emit_op >> BETA_TAC >> simp[rb_wrap_truncate])
  >>~- ([`comp_ignore_bind (emit_inst _ _ _) _`],
        irule rb_ignore >> simp[rb_emit_inst, rb_step_return])
  >>~- ([`rb_step rb_operand_ok (comp_bind (emit_op _ _) (\v. comp_bind _ _))`],
        irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
        irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >>~- ([`rb_step rb_operand_ok (comp_bind (emit_op _ _) (\v. emit_op _ _))`],
        irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >>~- ([`rb_step rb_operand_ok (comp_bind (if is_uint256 ty then _ else _) _)`],
        irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
        reverse conj_tac >- (Cases_on `is_uint256 ty` >> simp[rb_emit_op]) >>
        simp[rb_compile_select]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_bind_emit_op, rb_emit_op]
QED

Theorem rb_compile_bytestring_hash:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_bytestring_hash p)
Proof
  strip_tac >> pure_rewrite_tac[compile_bytestring_hash_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_emit_membership_eqs:
  !elems needle. EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step (EVERY rb_operand_ok) (emit_membership_eqs needle elems)
Proof
  Induct >> simp[emit_membership_eqs_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >>
  simp[rb_step_return]
QED

Theorem rb_fold_membership_or:
  !cs acc. EVERY rb_operand_ok cs /\ rb_operand_ok acc ==>
  rb_step rb_operand_ok (fold_membership_or acc cs)
Proof
  Induct >> simp[fold_membership_or_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[]
QED

Theorem rb_fold_membership_and:
  !cs acc. EVERY rb_operand_ok cs /\ rb_operand_ok acc ==>
  rb_step rb_operand_ok (fold_membership_and acc cs)
Proof
  Induct >> simp[fold_membership_and_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[]
QED

Theorem rb_compile_list_membership_in:
  EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step rb_operand_ok (compile_list_membership_in needle elems)
Proof
  strip_tac >> pure_rewrite_tac[compile_list_membership_in_def] >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_emit_membership_eqs] >>
  gen_tac >> Cases_on `x` >> simp[rb_step_return, rb_fold_membership_or]
QED

Theorem rb_compile_list_membership_notin:
  EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step rb_operand_ok (compile_list_membership_notin needle elems)
Proof
  strip_tac >> pure_rewrite_tac[compile_list_membership_notin_def] >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_emit_membership_eqs] >>
  gen_tac >> Cases_on `x` >> simp[rb_step_return] >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_fold_membership_and]
QED

Theorem rb_compile_mapping_subscript:
  rb_operand_ok slot /\ rb_operand_ok key ==>
  rb_step rb_operand_ok (compile_mapping_subscript slot key)
Proof
  strip_tac >> pure_rewrite_tac[compile_mapping_subscript_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_keccak256_key:
  rb_operand_ok key ==> rb_step rb_operand_ok (compile_keccak256_key key bytes32)
Proof
  strip_tac >> Cases_on `bytes32` >>
  simp[compile_keccak256_key_def]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_array_membership_loop:
  rb_operand_ok needle /\ rb_operand_ok arr /\ rb_operand_ok len /\
  (!p. rb_operand_ok p ==> rb_step rb_operand_ok (loader p)) ==>
  rb_step rb_operand_ok
    (compile_array_membership_loop needle arr len sz off loader bound is_in)
Proof
  strip_tac >> pure_rewrite_tac[compile_array_membership_loop_def] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `bound` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_inst]) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  suspend "body"
QED

Resume rb_compile_array_membership_loop[body]:
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `off > 0` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  Cases_on `is_in` >> simp[rb_step_return, rb_emit_op]
QED

Finalise rb_compile_array_membership_loop

Theorem rb_compile_var_array_membership:
  rb_env_ok ce /\ rb_operand_ok needle /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_var_array_membership ce needle vv ty is_in)
Proof
  strip_tac >> pure_rewrite_tac[compile_var_array_membership_def, LET_THM] >>
  BETA_TAC >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `(case ty of ArrayT _ (Dynamic _) => T | _ => F)` >>
      simp[]
      >- (irule rb_compile_ptr_load >> simp[rb_value_operand] >>
          gvs[rb_env_ok_def]) >>
      Cases_on `ty` >> simp[rb_step_return] >>
      rename1 `ArrayT et bd` >> Cases_on `bd` >> simp[rb_step_return]) >>
  gen_tac >> strip_tac >> irule rb_compile_array_membership_loop >>
  simp[rb_value_operand] >> gen_tac >> strip_tac >>
  irule rb_compile_ptr_load >> gvs[rb_env_ok_def]
QED

Theorem rb_compile_extcodesize_check:
  rb_operand_ok addr ==> rb_step (K T) (compile_extcodesize_check addr)
Proof
  strip_tac >> pure_rewrite_tac[compile_extcodesize_check_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_return_value_decode:
  rb_step rb_operand_ok (compile_return_value_decode min_size max_size)
Proof
  pure_rewrite_tac[compile_return_value_decode_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_select]
QED

(* Decoder antecedent: conjunct 1 of runtimeLabelABI$rb_abi_decode. *)
Theorem rb_compile_default_return_path:
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
     rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_operand_ok buf /\ rb_operand_ok result /\ rb_operand_ok default_op /\
  rb_operand_ok addr ==>
  rb_step rb_operand_ok
    (compile_default_return_path ce rty dty buf result default_op addr
       skip min_size max_size info)
Proof
  strip_tac >> pure_rewrite_tac[compile_default_return_path_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_store_memory] >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `skip` >> simp[rb_step_return, rb_compile_extcodesize_check]) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_return_value_decode] >>
  gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> simp[rb_new_block, rb_step_return]
QED

Theorem rb_compile_multi_vvs:
  !es. (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_value_ok) (compile_multi_vvs cfn ce es)
Proof
  Induct >> simp[compile_multi_vvs_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_extcall_store_values:
  !args buf off. rb_env_ok ce /\ EVERY (rb_value_ok o FST) args /\
  rb_operand_ok buf ==>
  rb_step (K T) (compile_extcall_store_values ce args buf off)
Proof
  Induct >> simp[compile_extcall_store_values_def, rb_step_return] >>
  gen_tac >> gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  pure_rewrite_tac[compile_extcall_store_values_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> reverse conj_tac >- simp[] >>
  Cases_on `is_word_type h1` >> simp[rb_emit_void] >>
  Cases_on `is_bytestring_type h1` >>
  simp[rb_emit_void, rb_compile_store_bytestring]
QED

(* ABI antecedents are rb_abi_encode conjunct 2 and rb_abi_decode conjunct 1. *)
Theorem rb_compile_external_call_kwargs:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
     rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_env_ok ce /\ EVERY (rb_value_ok o FST) (ZIP (avs,tys)) /\ rb_operand_ok addr /\
  rb_operand_ok value /\ rb_operand_ok gas /\ rb_operand_ok default_op ==>
  rb_step rb_operand_ok
    (compile_external_call_kwargs ce addr avs tys msz asz mid rsz minsz rmsz
       static value gas skip has_default default_op rty dty enc_info dec_info)
Proof
  strip_tac >> pure_rewrite_tac[compile_external_call_kwargs_def, LET_THM] >>
  BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- suspend "args" >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `rty = NoneT /\ ~skip` >>
      simp[rb_step_return, rb_compile_extcodesize_check]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `static` >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_ignore >> conj_tac
  >- (irule rb_ignore >> simp[rb_emit_void, rb_emit_inst]) >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  suspend "result"
QED

Resume rb_compile_external_call_kwargs[args]:
  Cases_on `avs = []` >> simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (irule rb_compile_extcall_store_values >> simp[]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> simp[rb_emit_op]
QED

Resume rb_compile_external_call_kwargs[result]:
  Cases_on `rty = NoneT` >> simp[rb_step_return] >>
  Cases_on `has_default` >> simp[]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_compile_default_return_path >> simp[]) >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_return_value_decode] >>
  gen_tac >> strip_tac >> irule rb_ignore >> simp[rb_step_return]
QED

Finalise rb_compile_external_call_kwargs

Theorem rb_compile_dynarray_append:
  !base v ce ws sz dty sty cap prim load store. rb_operand_ok base /\ rb_operand_ok v ==>
  rb_step (K T)
    (compile_dynarray_append ce base v ws sz dty sty cap prim load store)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_dynarray_append_def, LET_THM] >>
  BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `prim` >> simp[rb_emit_void] >>
      Cases_on `(case store of SSTORE => LocStorage | TSTORE => LocTransient
                   | _ => LocMemory) = LocMemory` >> simp[]
      >- (irule rb_ignore >> simp[rb_compile_store_memory, rb_step_return]) >>
      simp[cj 1 rb_slots]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_dynarray_pop:
  !base imm ws sz ctor loc. rb_operand_ok base /\ (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step rb_operand_ok (compile_dynarray_pop base ws sz ctor imm loc)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_dynarray_pop_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_ptr_load] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_ptr_store] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_store_multi_results:
  !ops buf off. EVERY rb_operand_ok ops /\ rb_operand_ok buf ==>
  rb_step (K T) (store_multi_results buf ops off)
Proof
  Induct >> simp[store_multi_results_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void]
QED

Theorem rb_compile_array_subscript:
  !base idx dyn count ws sz signed loader.
  rb_operand_ok base /\ rb_operand_ok idx /\
  (!p. rb_operand_ok p ==> rb_step rb_operand_ok (loader p)) ==>
  rb_step rb_operand_ok
    (compile_array_subscript base idx dyn count ws sz signed loader)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_array_subscript_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `dyn` >> simp[rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `signed` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `dyn` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_tuple_subscript:
  !base off. rb_operand_ok base ==>
  rb_step rb_operand_ok (compile_tuple_subscript base off)
Proof
  simp[compile_tuple_subscript_def, rb_emit_op]
QED

Theorem rb_compile_store_byte_chunks:
  !p bs off. rb_operand_ok p ==>
  rb_step (K T) (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def, rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void] >>
  gvs[]
QED

Theorem rb_compile_bytelike_literal:
  rb_step rb_buffer_ok (compile_bytelike_literal bs maxlen)
Proof
  pure_rewrite_tac[compile_bytelike_literal_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_ignore >> simp[rb_compile_store_byte_chunks, rb_step_return,
                          rb_buffer_ok_def]
QED

Theorem rb_compile_literal_vv:
  !ty lit. rb_step rb_value_ok (compile_literal_vv ty lit)
Proof
  gen_tac >> Cases >> simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def]
  >- (rename1 `BoolL b` >> Cases_on `b` >>
      simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def])
  >- (Cases_on `ty` >> simp[compile_literal_vv_def] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      simp[rb_compile_bytelike_literal, rb_step_return, rb_buffer_ok_def,
           base_ptr_def, rb_value_ok_def, rb_ptr_ok_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  simp[rb_compile_bytelike_literal, rb_step_return, rb_buffer_ok_def,
       base_ptr_def, rb_value_ok_def, rb_ptr_ok_def]
QED

Theorem rb_compile_name_vv:
  rb_env_ok ce ==> rb_step rb_value_ok (compile_name_vv ce ty id)
Proof
  strip_tac >> pure_rewrite_tac[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- (irule rb_ignore >> simp[rb_emit_inst, rb_step_return, rb_value_ok_def]) >>
  rename1 `SOME loc` >>
  `rb_location_ok loc` by (gvs[rb_env_ok_def] >> metis_tac[]) >>
  Cases_on `loc` >>
  gvs[rb_location_ok_def, rb_step_return, rb_value_ok_def, rb_mk_ptr] >>
  irule rb_ignore >> simp[rb_emit_inst, rb_step_return, rb_value_ok_def]
QED

Theorem rb_compile_env_var:
  !ev. rb_step rb_operand_ok (compile_env_var ev)
Proof
  Cases >> simp[compile_env_var_def, rb_emit_op] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_load_bytestring_as_word:
  rb_operand_ok v ==>
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (load_bytestring_as_word v opc)
Proof
  strip_tac >> pure_rewrite_tac[load_bytestring_as_word_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `opc = SAR` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]
QED

Theorem rb_compile_int_clamp:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_int_clamp signed bits v)
Proof
  strip_tac >> Cases_on `signed` >>
  simp[compile_int_clamp_def]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_bytestring_widen_copy:
  rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_bytestring_widen_copy dst_size v src_size)
Proof
  strip_tac >> pure_rewrite_tac[compile_bytestring_widen_copy_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> simp[rb_compile_copy_memory, rb_step_return]
QED

Theorem rb_compile_neg:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_neg v ty)
Proof
  strip_tac >> simp[compile_neg_def] >>
  Cases_on `type_bounds ty` >> simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_emit_void, rb_emit_op]
QED


Theorem rb_compile_store_words:
  !vs buf off. EVERY rb_operand_ok vs /\ rb_operand_ok buf ==>
  rb_step (K T) (compile_store_words buf vs off)
Proof
  Induct >> simp[compile_store_words_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `off = 0` >> simp[rb_step_return, rb_emit_op]) >>
  gen_tac >> strip_tac >> irule rb_ignore >> simp[rb_emit_void]
QED

Theorem rb_compile_invert:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_invert v ty ce)
Proof
  Cases_on `ty` >> simp[compile_invert_def, rb_emit_op]
QED

Theorem rb_compile_type_convert:
  !conv v. rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_type_convert v conv)
Proof
  Cases >> rpt strip_tac
  >~ [`compile_type_convert v ConvIdentity`] >- simp[compile_type_convert_def, rb_step_return]
  >~ [`compile_type_convert v ConvToBool`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >~ [`compile_type_convert v (ConvBoolToDecimal n)`]
  >- simp[compile_type_convert_def, rb_emit_op]
  >~ [`compile_type_convert v (ConvToFlag n)`]
  >- (Cases_on `n < 256` >> simp[compile_type_convert_def, rb_compile_int_clamp, rb_step_return])
  >~ [`compile_type_convert v ConvToAddress`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytestringCast n m)`]
  >- (simp[compile_type_convert_def] >> IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesMToBytesM n m)`]
  >- (simp[compile_type_convert_def] >> IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v ConvBytestringToBool`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[] >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >~ [`compile_type_convert v (ConvBytestringToBytesM n)`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[rb_emit_op])
  >~ [`compile_type_convert v (ConvBytestringToInt b n m)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[] >> strip_tac >> IF_CASES_TAC >>
      simp[rb_compile_int_clamp, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesToInt m b n)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- (Cases_on `b` >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> IF_CASES_TAC >> simp[rb_compile_int_clamp, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesToAddress n)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvIntToBytesM b n m)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      conj_tac >- simp[rb_emit_op] >>
      Cases_on `n > m * 8` >> simp[rb_step_return] >>
      Cases_on `b` >> simp[] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvIntToInt b n c m)`]
  >- (Cases_on `b` >> Cases_on `c` >>
      Cases_on `m < n` >> simp[compile_type_convert_def] >>
      simp[rb_compile_int_clamp, rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesMToDecimal m d lo hi)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytestringToDecimal d lo hi n)`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[] >> strip_tac >> IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvIntToDecimal b n d lo hi)`]
  >- suspend "int_decimal"
  >> suspend "decimal_int"
QED

Resume rb_compile_type_convert[int_decimal]:
  pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_void]) >>
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- (Cases_on `b` >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  simp[rb_emit_op]
QED

Resume rb_compile_type_convert[decimal_int]:
  pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_void]) >>
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- (Cases_on `b` >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  simp[rb_emit_op]
QED
Finalise rb_compile_type_convert

Theorem rb_compile_stage_intcall_args:
  !es flags tys. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_operand_ok) (compile_stage_intcall_args cfn ce es flags tys)
Proof
  Induct >> simp[compile_stage_intcall_args_def, rb_step_return] >>
  rpt strip_tac >> Cases_on `flags` >> Cases_on `tys` >>
  simp[compile_stage_intcall_args_def, LET_THM] >> BETA_TAC
  >~ [`compile_stage_intcall_args cfn ce (h::es) (flag::fs) (ty::ts)`]
  >- (Cases_on `flag` >> simp[compile_stage_intcall_args_def, LET_THM] >>
      BETA_TAC >- suspend "stack" >> suspend "memory")
  >> suspend "stack"
QED

Resume rb_compile_stage_intcall_args[stack]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (first_x_assum irule >> simp[]) >>
   simp[rb_step_return])
QED

Resume rb_compile_stage_intcall_args[memory]:
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_emit_void] >> IF_CASES_TAC >>
      simp[rb_compile_store_memory] >> irule rb_ignore >>
      simp[rb_compile_store_bytestring, rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED
Finalise rb_compile_stage_intcall_args

Theorem rb_lower_value:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce ty e) ==>
  rb_step rb_operand_ok (lower_value cfn ce ty e)
Proof
  strip_tac >> pure_rewrite_tac[lower_value_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >>
  BETA_TAC >> simp[rb_unwrap_value]
QED

Theorem rb_lower_value_with_loc:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce ty e) ==>
  rb_step (rb_operand_ok o FST) (lower_value_with_loc cfn ce ty e)
Proof
  strip_tac >> pure_rewrite_tac[lower_value_with_loc_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  BETA_TAC >> simp[rb_unwrap_value, rb_step_return]
QED

Theorem rb_compile_multi_exprs:
  !es. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_operand_ok) (compile_multi_exprs cfn ce es)
Proof
  Induct >> simp[compile_multi_exprs_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_attribute:
  rb_step rb_value_ok (cfn ce ty e) ==>
  rb_step rb_value_ok (compile_attribute cfn ce ret_ty ty e fld)
Proof
  strip_tac >> pure_rewrite_tac[compile_attribute_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_value_operand, rb_step_return, rb_value_ok_def, rb_mk_ptr]
QED

Theorem rb_compile_make_tuple:
  !es tys buf off. rb_env_ok ce /\ rb_operand_ok buf /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_make_tuple cfn ce es tys buf off)
Proof
  Induct >> simp[compile_make_tuple_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `tys` >> simp[compile_make_tuple_def, rb_step_return] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem rb_compile_make_array_elems:
  !es buf idx. rb_env_ok ce /\ rb_operand_ok buf /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok
    (compile_make_array_elems cfn ce es et sz has_len buf idx)
Proof
  Induct >> simp[compile_make_array_elems_def, rb_step_return] >> rpt strip_tac >>
  pure_rewrite_tac[compile_make_array_elems_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem rb_compile_make_array:
  rb_env_ok ce /\ rb_operand_ok buf /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_make_array cfn ce es et sz has_len buf)
Proof
  strip_tac >> pure_rewrite_tac[compile_make_array_def] >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `has_len` >> simp[rb_emit_void, rb_step_return]) >>
  simp[rb_compile_make_array_elems]
QED

Theorem rb_compile_struct_lit:
  !flds buf off. rb_env_ok ce /\ rb_operand_ok buf /\
  (!nm e. MEM (nm,e) flds ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_struct_lit cfn ce ty flds buf off)
Proof
  Induct >> simp[compile_struct_lit_def, rb_step_return] >> rpt strip_tac >>
  PairCases_on `h` >> pure_rewrite_tac[compile_struct_lit_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> qexists_tac `h0` >> simp[]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem rb_compile_store_abi_tuple:
  !args buf off. EVERY (rb_operand_ok o FST) args /\ rb_operand_ok buf ==>
  rb_step (K T) (compile_store_abi_tuple ce buf off args)
Proof
  Induct >> simp[compile_store_abi_tuple_def, rb_step_return] >> rpt strip_tac >>
  PairCases_on `h` >> gvs[] >>
  pure_rewrite_tac[compile_store_abi_tuple_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (Cases_on `is_word_type h1` >> simp[rb_emit_void, rb_compile_copy_memory]) >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_concat:
  !es infos. rb_env_ok ce /\ rb_operand_ok dp /\ rb_operand_ok offp /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (K T) (compile_concat cfn ce es dp infos offp)
Proof
  Induct >> simp[compile_concat_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `infos` >> simp[compile_concat_def, rb_step_return] >>
  PairCases_on `h'` >> simp[compile_concat_def] >>
  Cases_on `h'0` >> simp[]
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
      first_x_assum irule >> simp[]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_materialize_vv:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_materialize_vv ce ty vv)
Proof
  strip_tac >> pure_rewrite_tac[compile_materialize_vv_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_compile_store_memory, rb_step_return]
QED

Theorem rb_compile_ifexp_arm:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_ifexp_arm ce rty aty vv)
Proof
  strip_tac >> pure_rewrite_tac[compile_ifexp_arm_def] >>
  IF_CASES_TAC >- simp[rb_unwrap_value] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule rb_ignore >> simp[rb_compile_store_memory, rb_step_return]
QED

Theorem rb_compile_snapshot_vv:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_value_ok (compile_snapshot_vv ce copy vv)
Proof
  strip_tac >> pure_rewrite_tac[compile_snapshot_vv_def] >>
  IF_CASES_TAC
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      simp[rb_unwrap_value, rb_step_return, rb_value_ok_def]) >>
  Cases_on `copy` >> simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_materialize_vv, rb_step_return, rb_value_ok_def, rb_mk_ptr]
QED

Theorem rb_compile_abi_encode_args:
  !es. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_operand_ok) (compile_abi_encode_args cfn ce es)
Proof
  Induct >> simp[compile_abi_encode_args_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_materialize_vv, rb_unwrap_value]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_subscript:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce ty be) /\
  rb_step rb_value_ok (cfn ce (expr_type ie) ie) /\
  rb_step rb_value_ok (cfn ce ty ie) ==>
  rb_step rb_value_ok (compile_subscript cfn ce ret_ty ty be ie)
Proof
  strip_tac >> pure_rewrite_tac[compile_subscript_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_snapshot_vv, rb_step_return]) >>
  gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  reverse (Cases_on `place_type ce be`)
  >- (rename1 `ValPT bt` >> Cases_on `bt` >> simp[] >>
      pure_rewrite_tac[LET_THM] >> BETA_TAC
      >~ [`compile_tuple_subscript _ _`] >- suspend "tuple"
      >~ [`compile_tuple_subscript _ _`] >- suspend "tuple"
      >> suspend "array") >>
  simp[] >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_keccak256_key, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_mapping_subscript, rb_value_operand, rb_step_return,
       rb_value_ok_def, rb_mk_ptr]
QED

Resume rb_compile_subscript[tuple]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   simp[rb_compile_tuple_subscript, rb_value_operand, rb_step_return,
        rb_value_ok_def, rb_mk_ptr])
QED

Resume rb_compile_subscript[array]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   conj_tac >- simp[rb_step_return, rb_value_ok_def, rb_mk_ptr] >>
   irule rb_compile_array_subscript >> simp[rb_value_operand] >>
   gen_tac >> strip_tac >> irule rb_compile_ptr_load >> gvs[rb_env_ok_def])
QED
Finalise rb_compile_subscript

Theorem rb_every_zip_fst:
  !xs ys P. EVERY P xs ==> EVERY (P o FST) (ZIP (xs,ys))
Proof
  Induct >> Cases_on `ys` >> simp[listTheory.ZIP_def]
QED

Theorem rb_ext_call_arg_value:
  !vv. rb_value_ok vv ==> rb_value_ok (ext_call_arg_value ty vv)
Proof
  Cases >> simp[ext_call_arg_value_def, rb_value_ok_def]
QED

Theorem rb_compile_ext_call_args:
  !es tys. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_value_ok) (compile_ext_call_args cfn ce kws tys es)
Proof
  Induct >> simp[compile_ext_call_args_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `tys` >> simp[compile_ext_call_args_def, rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_snapshot_vv, rb_ext_call_arg_value] >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_ext_call_kwarg:
  rb_env_ok ce /\ (!ty. rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step (rb_operand_ok o FST) (compile_ext_call_kwarg cfn ce rty k e)
Proof
  strip_tac >> pure_rewrite_tac[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC
  >- (pure_rewrite_tac[LET_THM] >> BETA_TAC >>
      irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      simp[rb_compile_materialize_vv, rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_lower_value, rb_step_return]
QED

Theorem rb_compile_ext_call_kwargs:
  !es ks. rb_env_ok ce /\
  (!e ty. MEM e es ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step (\p. OPTION_ALL rb_operand_ok (FST p) /\
               OPTION_ALL rb_operand_ok (FST (SND p)) /\
               OPTION_ALL (rb_operand_ok o FST) (SND (SND p)))
    (compile_ext_call_kwargs cfn ce rty ks es)
Proof
  Induct >> simp[compile_ext_call_kwargs_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `ks` >> simp[compile_ext_call_kwargs_def, rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_ext_call_kwarg] >>
  Cases >> simp[] >> strip_tac >>
  irule rb_step_bind >>
  qexists_tac `\p. OPTION_ALL rb_operand_ok (FST p) /\
                   OPTION_ALL rb_operand_ok (FST (SND p)) /\
                   OPTION_ALL (rb_operand_ok o FST) (SND (SND p))` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  PairCases >> simp[] >> strip_tac >>
  rpt IF_CASES_TAC >> simp[rb_step_return]
QED

Theorem rb_compile_create_salt:
  !salt. rb_env_ok ce /\
  (!e. salt = SOME e ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (OPTION_ALL rb_operand_ok) (compile_create_salt cfn ce salt)
Proof
  Cases >> simp[compile_create_salt_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_lower_value, rb_step_return]
QED

Theorem rb_compile_create_ctor_tuple:
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_create_ctor_tuple cfn ce args)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_ctor_tuple_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `EVERY rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_multi_vvs] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> simp[rb_compile_extcall_store_values, rb_every_zip_fst, rb_step_return]
QED

(* Encoder antecedent: conjunct 2 of runtimeLabelABI$rb_abi_encode. *)
Theorem rb_compile_create_blueprint_args:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (compile_create_blueprint_args cfn ce raw args)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_args_def] >>
  Cases_on `raw` >> simp[]
  >- (Cases_on `args` >> simp[]
      >- (irule rb_ignore >> simp[rb_emit_inst, rb_step_return]) >>
      Cases_on `t` >> simp[]
      >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
          reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
          irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
          irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
      irule rb_ignore >> simp[rb_emit_inst, rb_step_return]) >>
  Cases_on `args = []` >> simp[rb_step_return] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_ctor_tuple] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_step_return]
QED

Theorem rb_compile_create_snapshot:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_create_snapshot ce vv ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_snapshot_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_ignore >> reverse conj_tac >- simp[rb_step_return] >>
  Cases_on `vv_location vv` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[rb_value_operand] >>
      gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
      simp[rb_value_operand, rb_compile_copy_memory_dynamic]) >>
  Cases_on `x'` >> simp[]
  >~ [`compile_imm_copy_to_memory _ _ _ _ _ _`]
  >- (irule rb_ignore >> conj_tac >- (irule rb_compile_imm_copy_to_memory >>
          gvs[rb_env_ok_def, rb_value_operand]) >> simp[rb_step_return])
  >~ [`compile_slot_to_memory _ _ _ _`]
  >- (irule rb_ignore >> simp[rb_compile_slot_to_memory, rb_value_operand, rb_step_return])
  >~ [`compile_slot_to_memory _ _ _ _`]
  >- (irule rb_ignore >> simp[rb_compile_slot_to_memory, rb_value_operand, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_value_operand] >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_value_operand, rb_compile_copy_memory_dynamic]
QED

Theorem rb_compile_raw_create:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce (expr_type be) be) /\
  rb_step rb_value_ok (cfn ce (expr_type ve) ve) /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) /\
  (!e. salt_e = SOME e ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_raw_create cfn ce be ve args salt_e rof)
Proof
  strip_tac >> pure_rewrite_tac[compile_raw_create_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_snapshot] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `args = []` >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_ignore >> conj_tac >- simp[rb_compile_copy_memory_dynamic] >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_create_ctor_tuple] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
  Cases >> simp[] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `OPTION_ALL rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_create_salt, rb_compile_create_dispatch] >>
  Cases >> simp[rb_compile_create_dispatch]
QED
