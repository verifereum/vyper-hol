(* Operand exclusion for byte slices, simple/system primitives and hashing.
   Unique owner of the foundational builtin boundaries used by later families. *)
Theory runtimeLabelBuiltinCore
Ancestors
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_slice_calldata:
  rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_calldata sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_calldata_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_slice_code:
  rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_code sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_code_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_slice_extcode:
  rb_operand_ok addr /\ rb_operand_ok sop /\ rb_operand_ok len ==>
  rb_step rb_operand_ok (compile_slice_extcode addr sop len n)
Proof
  strip_tac >> pure_rewrite_tac[compile_slice_extcode_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_slice_out_buf] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_extract32_load:
  rb_operand_ok src_len /\ rb_operand_ok src_data /\ rb_operand_ok sop ==>
  rb_step rb_operand_ok (compile_extract32_load src_len src_data sop)
Proof
  strip_tac >> pure_rewrite_tac[compile_extract32_load_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_assert_slice_bounds] >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[] >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_compile_zero_words,
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_compile_select]
QED

Theorem rb_compile_msg_data_to_memory:
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    compile_msg_data_to_memory
Proof
  pure_rewrite_tac[compile_msg_data_to_memory_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_dynamic] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  Cases_on `max_outsize > 0` >> simp[rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  simp[rb_emit_void, rb_step_return]
QED

Resume rb_compile_raw_call_finish[no_revert]:
  Cases_on `max_outsize > 0` >> simp[LET_THM, rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_mulmod:
  rb_operand_ok a /\ rb_operand_ok b /\ rb_operand_ok c ==>
  rb_step rb_operand_ok (compile_mulmod a b c)
Proof
  strip_tac >> pure_rewrite_tac[compile_mulmod_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_sha256_word:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_sha256_word v)
Proof
  strip_tac >> pure_rewrite_tac[compile_sha256_word_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_sha256_bytesm:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_sha256_bytesm v n)
Proof
  strip_tac >> pure_rewrite_tac[compile_sha256_bytesm_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED
