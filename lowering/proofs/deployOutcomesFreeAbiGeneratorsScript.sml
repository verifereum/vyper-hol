Theory deployOutcomesFreeAbiGenerators
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeGenerators deployOutcomesFreeArgs
  context emitHelper builtinAbi builtinBytes
  builtinSimple exprLowering abiEncoder list pair

val abi_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
    outcomes_free_fresh, outcomes_free_new_block, outcomes_free_alloc_buffer,
    outcomes_free_copy_memory]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_zero_words:
  !n s. P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_zero_words base_op n s)))
Proof
  Induct_on `n` >> rpt strip_tac >> simp[compile_zero_words_def] >>
  abi_preserve_tac >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_builtin_empty_complex:
  P ALLOCA /\ P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_empty_complex sz bs s)))
Proof
  strip_tac >> simp[compile_builtin_empty_complex_def] >>
  abi_preserve_tac >> simp[outcomes_free_zero_words]
QED

Theorem outcomes_free_bytestring_widen_copy:
  P ALLOCA /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_widen_copy sz v old s)))
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def] >> abi_preserve_tac
QED

Theorem outcomes_free_int_clamp:
  (!opc. MEM opc [SLT; SGT; GT; ISZERO; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_int_clamp sg bits v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_int_clamp_def] >> abi_preserve_tac
QED

Theorem outcomes_free_load_bytestring_as_word:
  (!opc. MEM opc [MLOAD; ADD; ISZERO; MUL; SUB; shift] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (load_bytestring_as_word v shift s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[load_bytestring_as_word_def] >> abi_preserve_tac
QED

Theorem outcomes_free_type_convert:
  (!opc. MEM opc [MLOAD; ADD; ISZERO; MUL; SUB; SHR; SAR; SLT; SGT; GT;
    AND; ASSERT; SIGNEXTEND; EQ; SHL; SDIV] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_type_convert v cv s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >> Cases_on `cv` >>
  simp[compile_type_convert_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_int_clamp,
    outcomes_free_load_bytestring_as_word, DISJ_IMP_THM, FORALL_AND_THM]),
    CHANGED_TAC abi_preserve_tac, pairarg_tac])
QED

Theorem outcomes_free_extract32_load:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; MLOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_extract32_load len data_op off s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_extract32_load_def, compile_assert_slice_bounds_def] >> abi_preserve_tac
QED

Theorem outcomes_free_clamp_basetype:
  (!opc. MEM opc [SHL; SLT; SGT; GT; ISZERO; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_clamp_basetype v ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `ty` >> simp[compile_clamp_basetype_def, outcomes_free_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[compile_clamp_basetype_def,
    outcomes_free_return, outcomes_free_clamp, DISJ_IMP_THM, FORALL_AND_THM]),
    CHANGED_TAC abi_preserve_tac, Cases_on `b`])
QED

Theorem outcomes_free_abi_encode_static:
  P MLOAD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_abi_encode_static dst src s)))
Proof
  strip_tac >> simp[compile_abi_encode_static_def] >> abi_preserve_tac
QED

Theorem outcomes_free_abi_encode_static_info:
  P MLOAD /\ P MSTORE /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_static_info dst src info s)))
Proof
  strip_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, outcomes_free_abi_encode_static] >>
  abi_preserve_tac
QED

Theorem outcomes_free_abi_encode_dyn_static_loop:
  (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
    ADD; MUL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_abi_encode_static_info]),
    CHANGED_TAC abi_preserve_tac])
QED

val abi_encode_case_tac =
  simp[Once compile_abi_encode_child_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_abi_encode_static,
    outcomes_free_abi_encode_dyn_static_loop, DISJ_IMP_THM, FORALL_AND_THM]),
    CHANGED_TAC abi_preserve_tac, CHANGED_TAC (gvs[]),
    first_x_assum irule]) >> gvs[];

Theorem outcomes_free_abi_encode:
  (!dst src info dyn off dp s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_child dst src info dyn off dp s)))) /\
  (!dst src info s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_to_buf dst src info s)))) /\
  (!dst src elems so ho dp s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_complex_elems dst src elems so ho dp s)))) /\
  (!dst src info asz msz len s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_dyn_loop dst src info asz msz len s))))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> abi_encode_case_tac
QED

Theorem outcomes_free_lower_abi_encode:
  (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
    ADD; MUL; AND; NOT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_abi_encode (ensure:bool) mid src info sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `mid` >> simp[lower_abi_encode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM]
    (cj 2 outcomes_free_abi_encode)]), CHANGED_TAC abi_preserve_tac])
QED

Theorem outcomes_free_lower_abi_decode:
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (lower_abi_decode src info lo hi sz s)))
Proof
  strip_tac >> simp[lower_abi_decode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cj 1 outcomes_free_abi_decode]),
    CHANGED_TAC abi_preserve_tac])
QED
