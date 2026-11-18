(* Safe callback-free dispatcher memory operations. *)
Theory ctorCallFreeMemory
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  builtinSimple builtinHashing builtinBytes builtinStrings
  ctorCallFreeRules ctorCallFreeValues

Theorem outcomes_free_compile_assert_slice_bounds:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_assert_slice_bounds a b c s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_assert_slice_bounds_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void]),
    gen_tac, strip_tac, irule every_state_insts_bind])
QED

val memory_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    outcomes_free_alloc_buffer, outcomes_free_copy_memory, outcomes_free_ptr_load,
    every_state_insts_fresh_id, every_state_insts_fresh_var,
    every_state_insts_fresh_label, every_state_insts_new_block,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_assert_slice_bounds]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_compile_builtin_len:
  (!opc. MEM opc [ADD; ILOAD; DLOAD; MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_len ctor imm v loc s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_builtin_len_def, outcomes_free_ptr_load]
QED

Theorem opcode_every_builtin_len:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_len ctor imm ptr_op loc st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_builtin_len >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_zero_words:
  !n s. P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_zero_words base_op n s)))
Proof
  Induct_on `n` >> rpt strip_tac >> simp[compile_zero_words_def] >>
  memory_preserve_tac >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_builtin_empty_complex:
  P ALLOCA /\ P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_empty_complex sz bs s)))
Proof
  strip_tac >> simp[compile_builtin_empty_complex_def] >>
  memory_preserve_tac >> simp[outcomes_free_zero_words]
QED

Theorem opcode_every_empty_complex:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_empty_complex sz bs st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_builtin_empty_complex >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_bytestring_widen_copy:
  P ALLOCA /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_widen_copy sz v old s)))
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def] >> memory_preserve_tac
QED

Theorem opcode_every_bytestring_widen_copy:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_widen_copy dst_size v src_size st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_bytestring_widen_copy >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_compile_keccak256_word:
  P ALLOCA /\ P MSTORE /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_word v s)))
Proof
  strip_tac >> simp[compile_keccak256_word_def] >> memory_preserve_tac
QED

Theorem outcomes_free_compile_keccak256_bytesm:
  P ALLOCA /\ P MSTORE /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_bytesm v n s)))
Proof
  strip_tac >> simp[compile_keccak256_bytesm_def] >> memory_preserve_tac
QED

Theorem outcomes_free_compile_keccak256_bytes:
  P MLOAD /\ P ADD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_bytes v s)))
Proof
  strip_tac >> simp[compile_keccak256_bytes_def] >> memory_preserve_tac
QED

Theorem outcomes_free_compile_bytestring_hash:
  P MLOAD /\ P ADD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytestring_hash v s)))
Proof
  strip_tac >> simp[compile_bytestring_hash_def] >> memory_preserve_tac
QED

Theorem opcode_every_keccak:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!v st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_keccak256_word v st)))) /\
  (!v m st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_keccak256_bytesm v m st)))) /\
  (!v st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_keccak256_bytes v st)))) /\
  (!v st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_bytestring_hash v st))))
  )
Proof
  rpt strip_tac >>
  simp[outcomes_free_compile_keccak256_word, outcomes_free_compile_keccak256_bytesm,
    outcomes_free_compile_keccak256_bytes, outcomes_free_compile_bytestring_hash]
QED

Theorem outcomes_free_compile_method_id_hash:
  (!opc. MEM opc [ALLOCA; MSTORE; SHA3; MLOAD; ADD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_method_id_hash ty v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `ty` >> simp[compile_method_id_hash_def, outcomes_free_compile_keccak256_bytes] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, outcomes_free_compile_keccak256_bytes] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_method_id_hash_def, outcomes_free_compile_keccak256_bytes,
    outcomes_free_compile_keccak256_bytesm]
QED

Theorem outcomes_free_compile_method_id_runtime:
  (!opc. MEM opc [ALLOCA; MSTORE; SHA3; MLOAD; ADD; SHR; SHL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_method_id_runtime ty v is_bytes4 s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_method_id_runtime_def] >> irule every_state_insts_bind >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_method_id_hash] >>
  rpt strip_tac >> memory_preserve_tac
QED

Theorem opcode_every_method_id_runtime:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_method_id_runtime ty v bytes4 st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_method_id_runtime >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_compile_bytestring_src:
  P MLOAD /\ P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytestring_src a s)))
Proof
  strip_tac >> simp[compile_bytestring_src_def] >> memory_preserve_tac
QED

Theorem opcode_every_bytestring_src:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_src src st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_bytestring_src >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_compile_slice_out_buf:
  P ALLOCA /\ P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_out_buf sz s)))
Proof
  strip_tac >> simp[compile_slice_out_buf_def] >> memory_preserve_tac
QED

Theorem opcode_every_slice_out_buf:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_slice_out_buf out_size st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_slice_out_buf >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_compile_slice_data:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; MCOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_data a b c d sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_data_def] >> memory_preserve_tac
QED

Theorem opcode_every_slice_data:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_slice_data src_len src_data start len out_size st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_slice_data >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_compile_slice_calldata:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; CALLDATASIZE; CALLDATACOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_calldata a b sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_calldata_def, compile_slice_out_buf_def] >>
  memory_preserve_tac >> pairarg_tac >> gvs[] >> memory_preserve_tac
QED

Theorem outcomes_free_compile_slice_code:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; CODESIZE; CODECOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_code a b sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_code_def, compile_slice_out_buf_def] >>
  memory_preserve_tac >> pairarg_tac >> gvs[] >> memory_preserve_tac
QED

Theorem outcomes_free_compile_slice_extcode:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; EXTCODESIZE; EXTCODECOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_extcode a b c sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_extcode_def, compile_slice_out_buf_def] >> memory_preserve_tac >>
  pairarg_tac >> gvs[] >> memory_preserve_tac
QED

Theorem opcode_every_slice_adhoc:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!start len out_size st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_slice_calldata start len out_size st)))) /\
  (!start len out_size st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_slice_code start len out_size st)))) /\
  (!addr start len out_size st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_slice_extcode addr start len out_size st))))
  )
Proof
  rpt strip_tac >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_slice_calldata,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_slice_code,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_slice_extcode]
QED

Theorem outcomes_free_extract32_load:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; MLOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_extract32_load len data_op off s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_extract32_load_def] >>
  rpt (FIRST [CHANGED_TAC (simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM]
    outcomes_free_compile_assert_slice_bounds]), CHANGED_TAC memory_preserve_tac])
QED

Theorem opcode_every_extract32_load:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_extract32_load src_len src_data start st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_extract32_load >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_compile_uint2str:
  (!opc. MEM opc [ALLOCA; ASSIGN; JMP; EQ; JNZ; Mod; ADD; SUB; MSTORE; Div] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_uint2str v n sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_uint2str_def] >> memory_preserve_tac
QED

Theorem opcode_every_uint2str:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_uint2str v nd sz st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_uint2str >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED
