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
