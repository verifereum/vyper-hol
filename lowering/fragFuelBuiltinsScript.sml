(*
 * Fuel bounds (fuel_ok) for the compile helpers of the built-in functions.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_select, fuel_ok_compile_builtin_len,
 *   fuel_ok_compile_builtin_calldatasize, fuel_ok_compile_builtin_empty_prim,
 *   fuel_ok_compile_zero_words, fuel_ok_compile_builtin_empty_complex,
 *   fuel_ok_compile_builtin_min, fuel_ok_compile_builtin_max,
 *   fuel_ok_compile_builtin_abs,
 *   fuel_ok_compile_unsafe_binop, fuel_ok_compile_unsafe_add/sub/mul/div,
 *   fuel_ok_compile_pow_mod256, fuel_ok_compile_addmod,
 *   fuel_ok_compile_mulmod, fuel_ok_compile_shift,
 *   fuel_ok_compile_msg_data_to_memory, fuel_ok_compile_raw_call_outbuf,
 *   fuel_ok_compile_raw_call_finish, fuel_ok_compile_send,
 *   fuel_ok_compile_raw_revert, fuel_ok_compile_selfdestruct,
 *   fuel_ok_compile_assert_slice_bounds, fuel_ok_compile_bytestring_src,
 *   fuel_ok_compile_slice_data, fuel_ok_compile_slice_out_buf,
 *   fuel_ok_compile_slice_calldata, fuel_ok_compile_slice_code,
 *   fuel_ok_compile_slice_extcode, fuel_ok_compile_extract32_load,
 *   fuel_ok_compile_keccak256_word/bytes/bytesm,
 *   fuel_ok_compile_method_id_hash, fuel_ok_compile_method_id_runtime,
 *   fuel_ok_compile_sha256_word/bytes/bytesm,
 *   fuel_ok_emit_void_selfdestruct, fuel_ok_uncurry_arg (generic rules)
 *   (fuel_ok_compile_uint2str is in fragFuelLoopUint2str)
 *)

Theory fragFuelBuiltins
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst venomExecSemantics venomState builtinSimple builtinMath
  builtinSystem builtinBytes
  builtinHashing builtinStrings fragFuelLoopUint2str
Libs
  fragFuelLib

(* Generic rule the framework lacks: a pair pattern bind
   `(a, b) <- m; k a b` leaves `UNCURRY k x`. *)
Theorem fuel_ok_uncurry_arg:
  !k x Wv L E.
    (!a b. fuel_ok Wv L E (k a b)) ==> fuel_ok Wv L E (UNCURRY k x)
Proof
  rpt strip_tac >> Cases_on `x` >> simp[]
QED

Theorem fuel_ok_compile_select:
  !c a b Wv E. fuel_ok Wv {} E (compile_select c a b)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_select_def] >>
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_builtin_len:
  !is_ctor imm ptr loc Wv E.
    fuel_ok Wv {} E (compile_builtin_len is_ctor imm ptr loc)
Proof
  simp[compile_builtin_len_def, fuel_ok_compile_ptr_load]
QED

Theorem fuel_ok_compile_builtin_calldatasize:
  !Wv E. fuel_ok Wv {} E compile_builtin_calldatasize
Proof
  rpt gen_tac >> simp_tac std_ss [compile_builtin_calldatasize_def] >>
  match_mp_tac fuel_ok_emit_op >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_builtin_empty_prim:
  !Wv E. fuel_ok Wv {} E compile_builtin_empty_prim
Proof
  simp[compile_builtin_empty_prim_def, comp_return_def, fuel_ok_return]
QED

Theorem fuel_ok_compile_zero_words:
  !n base Wv E. fuel_ok Wv {} E (compile_zero_words base n)
Proof
  Induct >> simp_tac std_ss [compile_zero_words_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_builtin_empty_complex:
  !size b Wv E. fuel_ok Wv {} E (compile_builtin_empty_complex size b)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_builtin_empty_complex_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_zero_words] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_builtin_min:
  !a b u Wv E. fuel_ok Wv {} E (compile_builtin_min a b u)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_builtin_min_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_select] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_builtin_max:
  !a b u Wv E. fuel_ok Wv {} E (compile_builtin_max a b u)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_builtin_max_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_select] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_builtin_abs:
  !v Wv E. fuel_ok Wv {} E (compile_builtin_abs v)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_builtin_abs_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_select] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_unsafe_binop:
  !opc x y bits s Wv E.
    ~is_terminator opc /\ opc <> PHI ==>
    fuel_ok Wv {} E (compile_unsafe_binop opc x y bits s)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [compile_unsafe_binop_def] >>
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_unsafe_arith:
  (!x y bits s Wv E. fuel_ok Wv {} E (compile_unsafe_add x y bits s)) /\
  (!x y bits s Wv E. fuel_ok Wv {} E (compile_unsafe_sub x y bits s)) /\
  (!x y bits s Wv E. fuel_ok Wv {} E (compile_unsafe_mul x y bits s)) /\
  (!x y bits s Wv E. fuel_ok Wv {} E (compile_unsafe_div x y bits s))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_unsafe_add_def, compile_unsafe_sub_def,
                   compile_unsafe_mul_def, compile_unsafe_div_def] >>
  match_mp_tac fuel_ok_compile_unsafe_binop >>
  rw[is_terminator_def]
QED

Theorem fuel_ok_compile_pow_mod256:
  !b e Wv E. fuel_ok Wv {} E (compile_pow_mod256 b e)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_pow_mod256_def] >>
  match_mp_tac fuel_ok_emit_op >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_addmod:
  !a b c Wv E. fuel_ok Wv {} E (compile_addmod a b c)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_addmod_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_mulmod:
  !a b c Wv E. fuel_ok Wv {} E (compile_mulmod a b c)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_mulmod_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_shift:
  !v b s Wv E. fuel_ok Wv {} E (compile_shift v b s)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_shift_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_select] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_msg_data_to_memory:
  !Wv E. fuel_ok Wv {} E compile_msg_data_to_memory
Proof
  rpt gen_tac >> simp_tac std_ss [compile_msg_data_to_memory_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_dynamic] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_raw_call_outbuf:
  !n Wv E. fuel_ok Wv {} E (compile_raw_call_outbuf n)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_raw_call_outbuf_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_raw_call_finish:
  !to dp dl gas v cty mo rof ov op Wv E.
    fuel_ok Wv {} E
      (compile_raw_call_finish to dp dl gas v cty mo rof ov op)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_raw_call_finish_def] >>
  Cases_on `cty` >> simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_emit_inst_jnz, fuel_ok_emit_inst_halt,
             fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_select] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_send:
  !to v gas Wv E. fuel_ok Wv {} E (compile_send to v gas)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_send_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_raw_revert:
  !p Wv E. fuel_ok Wv {} E (compile_raw_revert p)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_raw_revert_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_any] >>
  simp[is_terminator_def]
QED

(* Generic rule the framework lacks: SELFDESTRUCT is a terminator that never
   steps to OK without halting (framework has it only for the RETURN family). *)
Theorem fuel_ok_emit_void_selfdestruct:
  !ops Wv E. fuel_ok Wv {} E (emit_void SELFDESTRUCT ops)
Proof
  rpt gen_tac >>
  `emit_void SELFDESTRUCT ops = emit_inst SELFDESTRUCT ops []` by
    simp[emit_void_def, emit_inst_def] >>
  pop_assum SUBST1_TAC >>
  simp_tac std_ss [emit_inst_def] >>
  match_mp_tac fuel_ok_bind0 >> (conj_tac >- simp[fuel_ok_prims]) >>
  gen_tac >> BETA_TAC >> match_mp_tac fuel_ok_emit_halt >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem fuel_ok_compile_selfdestruct:
  !t Wv E. fuel_ok Wv {} E (compile_selfdestruct t)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_selfdestruct_def] >>
  MATCH_ACCEPT_TAC fuel_ok_emit_void_selfdestruct
QED

Theorem fuel_ok_compile_assert_slice_bounds:
  !s l n Wv E. fuel_ok Wv {} E (compile_assert_slice_bounds s l n)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_assert_slice_bounds_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_bytestring_src:
  !p Wv E. fuel_ok Wv {} E (compile_bytestring_src p)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_bytestring_src_def] >>
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_slice_data:
  !sl sd s l os Wv E. fuel_ok Wv {} E (compile_slice_data sl sd s l os)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_slice_data_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_assert_slice_bounds] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_slice_out_buf:
  !os Wv E. fuel_ok Wv {} E (compile_slice_out_buf os)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_slice_out_buf_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_slice_calldata:
  !s l os Wv E. fuel_ok Wv {} E (compile_slice_calldata s l os)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_slice_calldata_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_slice_out_buf, fuel_ok_uncurry_arg,
             fuel_ok_compile_assert_slice_bounds] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_slice_code:
  !s l os Wv E. fuel_ok Wv {} E (compile_slice_code s l os)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_slice_code_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_slice_out_buf, fuel_ok_uncurry_arg,
             fuel_ok_compile_assert_slice_bounds] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_slice_extcode:
  !a s l os Wv E. fuel_ok Wv {} E (compile_slice_extcode a s l os)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_slice_extcode_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_slice_out_buf, fuel_ok_uncurry_arg,
             fuel_ok_compile_assert_slice_bounds] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_extract32_load:
  !sl sd s Wv E. fuel_ok Wv {} E (compile_extract32_load sl sd s)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_extract32_load_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_assert_slice_bounds] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_keccak256:
  (!v Wv E. fuel_ok Wv {} E (compile_keccak256_word v)) /\
  (!p Wv E. fuel_ok Wv {} E (compile_keccak256_bytes p)) /\
  (!v m Wv E. fuel_ok Wv {} E (compile_keccak256_bytesm v m))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_keccak256_word_def, compile_keccak256_bytes_def,
                   compile_keccak256_bytesm_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_method_id_hash:
  !ty v Wv E. fuel_ok Wv {} E (compile_method_id_hash ty v)
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[compile_method_id_hash_def, fuel_ok_compile_keccak256] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, fuel_ok_compile_keccak256] >>
  rename1 `BytesT bt2` >> Cases_on `bt2` >>
  simp[compile_method_id_hash_def, fuel_ok_compile_keccak256]
QED

Theorem fuel_ok_compile_method_id_runtime:
  !ty v b4 Wv E. fuel_ok Wv {} E (compile_method_id_runtime ty v b4)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_method_id_runtime_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_method_id_hash] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_sha256:
  (!v Wv E. fuel_ok Wv {} E (compile_sha256_word v)) /\
  (!p Wv E. fuel_ok Wv {} E (compile_sha256_bytes p)) /\
  (!v m Wv E. fuel_ok Wv {} E (compile_sha256_bytesm v m))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_sha256_word_def, compile_sha256_bytes_def,
                   compile_sha256_bytesm_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED
