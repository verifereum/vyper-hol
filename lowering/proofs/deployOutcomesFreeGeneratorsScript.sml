Theory deployOutcomesFreeGenerators
Ancestors
  deployOutcomesFreeLowering exprLowering context emitHelper compileEnv
  exprBopLowering builtinSimple list pair venomInst

Theorem outcomes_free_as_ptr_val:
  SND (as_ptr_val ty loc m) = SND m
Proof
  Cases_on `m` >> simp[as_ptr_val_def]
QED

Theorem outcomes_free_alloc_buffer:
  P ALLOCA /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_alloc_buffer sz s)))
Proof
  rpt strip_tac >> simp[compile_alloc_buffer_def] >>
  irule outcomes_free_bind >> simp[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_imm_load:
  P ADD /\ P ILOAD /\ P DLOAD /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_load_word ctor imm off s)))
Proof
  rpt strip_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, outcomes_free_emit_ops] >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_ptr_load:
  P ADD /\ P ILOAD /\ P DLOAD /\ P MLOAD /\ P SLOAD /\
  P TLOAD /\ P CALLDATALOAD /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_load ctor imm loc off s)))
Proof
  rpt strip_tac >> Cases_on `loc` >>
  simp[compile_ptr_load_def, outcomes_free_emit_ops, outcomes_free_imm_load]
QED

Theorem outcomes_free_imm_store:
  P ADD /\ P ISTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_word imm off v s)))
Proof
  rpt strip_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, outcomes_free_emit_ops] >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_ptr_store:
  P ADD /\ P ISTORE /\ P INVALID /\ P MSTORE /\ P SSTORE /\ P TSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_store ctor imm loc off v s)))
Proof
  rpt strip_tac >> Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, outcomes_free_emit_ops, outcomes_free_imm_store]
QED

Theorem outcomes_free_copy_memory:
  P MCOPY /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory dst src sz s)))
Proof
  Cases_on `sz` >> simp[compile_copy_memory_def, outcomes_free_return,
    outcomes_free_emit_ops]
QED

Theorem outcomes_free_word_copy_base:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords load store ctor imm s)))
Proof
  strip_tac >> simp[compile_word_copy_loop_base_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
               outcomes_free_fresh, outcomes_free_new_block,
               outcomes_free_ptr_load, outcomes_free_ptr_store]),
       gen_tac, strip_tac, irule outcomes_free_bind,
       irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  gvs[]
QED

Theorem outcomes_free_word_copy:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords load store ctor s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_op src dst nwop load store ctor s)))
Proof
  strip_tac >> simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def] >>
  conj_tac >> irule outcomes_free_word_copy_base >> simp[]
QED

Theorem outcomes_free_lit_offset:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_lit_byte_offset op off s)))
Proof
  rpt strip_tac >> Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_imm_copy:
  !n off s. P ADD /\ P ILOAD /\ P DLOAD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off s)))
Proof
  Induct_on `n` >> rpt strip_tac >>
  simp[compile_imm_copy_to_memory_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_lit_offset,
          outcomes_free_imm_load, outcomes_free_emit_ops]),
       gen_tac, strip_tac, irule outcomes_free_bind,
       irule outcomes_free_ignore_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_as_stack_val:
  SND (as_stack_val ty m) = SND m
Proof
  Cases_on `m` >> simp[as_stack_val_def]
QED

Theorem outcomes_free_slot_copies:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_storage_to_memory src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_memory_to_storage src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_transient_to_memory src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_memory_to_transient src dst n s)))
Proof
  strip_tac >> simp[compile_storage_to_memory_def, compile_memory_to_storage_def,
    compile_transient_to_memory_def, compile_memory_to_transient_def,
    outcomes_free_word_copy]
QED

Theorem outcomes_free_ensure_memory:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc bytes words ctor imm s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `loc` >> simp[compile_ensure_in_memory_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_alloc_buffer, outcomes_free_imm_copy,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_slot_copies]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> gvs[]
QED

Theorem outcomes_free_unwrap_value:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value cenv vv s)))
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def, outcomes_free_return] >>
  IF_CASES_TAC >- simp[outcomes_free_ptr_load] >>
  Cases_on `p.ptr_location` >>
  simp[outcomes_free_return, outcomes_free_ensure_memory]
QED

Theorem outcomes_free_lower_value_opcodes:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
       EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn cenv ty e s)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (lower_value cfn cenv ty e s)))
Proof
  strip_tac >> simp[lower_value_def] >> irule outcomes_free_bind >>
  simp[outcomes_free_unwrap_value]
QED

Theorem outcomes_free_clamp:
  (!opc. MEM opc [SLT; SGT; ISZERO; AND; GT; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_clamp v ty s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (clamp_and_return v ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `type_bounds ty` >> simp[clamp_and_return_def, compile_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_safe_add_sub:
  (!opc. MEM opc [ADD; SUB; SLT; SGT; ISZERO; AND; GT; ASSERT; LT; EQ] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_add x y ty s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_sub x y ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_safe_add_def, compile_safe_sub_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_mul_check:
  (!opc. MEM opc [SDIV; Div; EQ; ISZERO; OR; NOT; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_mul_overflow_check x y res signed bits s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `signed` >> simp[compile_mul_overflow_check_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_safe_mul:
  (!opc. MEM opc [MUL; SDIV; Div; EQ; ISZERO; OR; NOT; AND; ASSERT; SLT; SGT; GT]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_mul x y ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_safe_mul_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_mul_check]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_safe_div_mod:
  (!opc. MEM opc [MUL; SDIV; Div; SMOD; Mod; EQ; ISZERO; NOT; AND; ASSERT; SLT; SGT; GT]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_div x y ty s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_decimal_div x y divisor ty s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_mod x y ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_safe_div_def, compile_safe_decimal_div_def, compile_safe_mod_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_safe_pow:
  (!opc. MEM opc [Exp; SLT; SGT; ISZERO; AND; GT; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_safe_pow x y ty base_literal exp_literal s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `base_literal` >> Cases_on `exp_literal` >> simp[compile_safe_pow_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_compare:
  (!opc. MEM opc [SLT; SGT; LT; GT; EQ; ISZERO; INVALID] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_compare bop x y ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `bop` >> simp[compile_compare_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_wrap_truncate:
  P SIGNEXTEND /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (wrap_truncate res ty s)))
Proof
  strip_tac >> simp[wrap_truncate_def] >>
  rpt IF_CASES_TAC >> simp[outcomes_free_emit_ops, outcomes_free_return]
QED

Theorem outcomes_free_binop:
  (!opc. MEM opc [ADD; SUB; MUL; SDIV; Div; SMOD; Mod; EQ; ISZERO; OR; NOT;
    AND; ASSERT; SLT; SGT; GT; LT; Exp; SIGNEXTEND; XOR; SHL; SAR; SHR; INVALID]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_binop bop x y ty base_literal exp_literal s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `bop` >> simp[compile_binop_def, compile_select_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_wrap_truncate,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_add_sub,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_mul,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_div_mod,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_pow,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compare]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_lower_value_with_loc:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
       EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn cenv ty e s)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (lower_value_with_loc cfn cenv ty e s)))
Proof
  strip_tac >> simp[lower_value_with_loc_def] >>
  irule outcomes_free_bind >> simp[] >> rpt strip_tac >>
  irule outcomes_free_bind >> simp[outcomes_free_return, outcomes_free_unwrap_value]
QED

Theorem outcomes_free_imm_store_words:
  !n off s. P ADD /\ P MLOAD /\ P ISTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_words imm src dst n off s)))
Proof
  Induct_on `n` >> rpt strip_tac >>
  simp[compile_imm_store_words_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_lit_offset,
    outcomes_free_imm_store, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_zero_memory_loop:
  !ptr_op i words s. P ADD /\ P MSTORE /\
  EVERY (\j. P j.inst_opcode) (state_insts s) ==>
  EVERY (\j. P j.inst_opcode)
    (state_insts (SND (compile_zero_memory_loop ptr_op i words s)))
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  simp[Once compile_zero_memory_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC, first_assum irule])
QED

Theorem outcomes_free_zero_memory:
  P ADD /\ P MSTORE /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_zero_memory ptr_op sz s)))
Proof
  Cases_on `sz` >> simp[compile_zero_memory_def, outcomes_free_return,
    outcomes_free_zero_memory_loop]
QED

Theorem outcomes_free_context_loads:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE] ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_storage src prim n sz s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_transient src prim n sz s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_code_to_memory src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_immutable src prim n sz ctor s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_load_storage_def, compile_load_transient_def,
    compile_code_to_memory_def, compile_load_immutable_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_alloc_buffer, compile_code_to_memory_def,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_slot_copies,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_word_copy]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_nonreentrant:
  (!opc. MEM opc [TLOAD; SLOAD; TSTORE; SSTORE; EQ; ISZERO; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_lock key trans view s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_unlock key trans view s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_bytestring_copy:
  P MLOAD /\ P NOT /\ P ADD /\ P AND /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_copy_len src s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_bytestring src dst s)))
Proof
  strip_tac >> simp[compile_bytestring_copy_len_def, compile_store_bytestring_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    compile_bytestring_copy_len_def]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac])
QED

Theorem outcomes_free_byte_offset:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_with_byte_offset src off s)))
Proof
  strip_tac >> simp[compile_with_byte_offset_def] >>
  IF_CASES_TAC >> simp[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_typed_copy:
  (!opc. MEM opc [MLOAD; MSTORE; NOT; ADD; AND; MCOPY; INVALID; ASSIGN;
    JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT] ==> P opc) ==>
  (!ce dst dt src st s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory_typed ce dst dt src st s)))) /\
  (!ce dst src dts sts doff soff s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_typed_copy_fields ce dst src dts sts doff soff s)))) /\
  (!ce dst dt src st n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_sarray_typed ce dst dt src st n s)))) /\
  (!ce dst dt cap src st s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_dynarray_typed ce dst dt cap src st s)))) /\
  (!ce dst src dfs sfs doff soff s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff s))))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt strip_tac
  >- (simp[Once compile_store_memory_typed_def] >>
      Cases_on `is_word_type dt`
      >- (simp[] >> irule outcomes_free_bind >> simp[outcomes_free_emit_ops]) >>
      Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
      >- simp[outcomes_free_bytestring_copy] >>
      Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
      >- (Cases_on `dt` >> Cases_on `st` >> gvs[] >>
          rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> simp[outcomes_free_copy_memory]) >>
      simp[outcomes_free_emit_ops]) >>
  simp[Once compile_store_memory_typed_def] >> gnvs[] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_fresh, outcomes_free_new_block, outcomes_free_byte_offset,
    outcomes_free_copy_memory, outcomes_free_bytestring_copy,
    compile_copy_memory_dynamic_def]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC,
    first_assum (fn th => irule th >> simp[] >> NO_TAC), pairarg_tac]) >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

Theorem outcomes_free_store_memory:
  (!opc. MEM opc [MLOAD; MSTORE; NOT; ADD; AND; MCOPY; INVALID; ASSIGN;
    JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_memory ce src dst dt st s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[outcomes_free_emit_ops, outcomes_free_copy_memory, outcomes_free_bytestring_copy,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] (cj 1 outcomes_free_typed_copy)]
QED

Theorem outcomes_free_alloc_dynamic:
  P DALLOCA /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_dynamic sz s)))
Proof
  simp[compile_alloc_dynamic_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_fixed_region:
  P ASSIGN /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_fixed_region_with_id sz s)))
Proof
  simp[compile_fixed_region_with_id_def, fresh_id_def, fresh_var_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, outcomes_free_emit,
    outcomes_free_state_insts, mk_inst_def, emit_def]
QED

Theorem outcomes_free_bytestring_word_count:
  P MLOAD /\ P ADD /\ P SHR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_word_count src s)))
Proof
  strip_tac >> simp[compile_bytestring_word_count_def] >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops] >> rpt strip_tac >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_store_immutable_bytestring:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
    SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE; TSTORE; SHR]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_immutable_bytestring imm src dst s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_store_immutable_bytestring_def] >>
  irule outcomes_free_bind >> simp[outcomes_free_bytestring_word_count] >>
  rpt strip_tac >> irule outcomes_free_ignore_bind >>
  simp[outcomes_free_return,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_word_copy_base]
QED

Theorem outcomes_free_slot_to_memory:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
    SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE; TSTORE]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_slot_to_memory src dst n loc s)))
Proof
  strip_tac >> simp[compile_slot_to_memory_def] >>
  irule (cj 1 outcomes_free_word_copy) >> simp[]
QED

Theorem outcomes_free_copy_memory_dynamic:
  P MCOPY /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory_dynamic dst src len s)))
Proof
  simp[compile_copy_memory_dynamic_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_encode_log_topic:
  P ADD /\ P MLOAD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_encode_log_topic src bytestring s)))
Proof
  strip_tac >> Cases_on `bytestring` >>
  simp[compile_encode_log_topic_def, outcomes_free_return] >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops] >> rpt strip_tac >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_load_memory:
  P MLOAD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_memory src prim s)))
Proof
  strip_tac >> Cases_on `prim` >>
  simp[compile_load_memory_def, outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_dynarray_to_storage:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
    SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE; TSTORE; LT; ISZERO]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_dynarray_to_storage src dst words sz trans s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `trans` >> simp[compile_dynarray_to_storage_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_fresh, outcomes_free_new_block,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_word_copy]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED
