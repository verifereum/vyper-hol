(* Opcode bounds for runtime-default evaluation and memory stores. *)
Theory runtimeDefaultRejectCode
Ancestors
  ctorCallFreeCallbacks ctorCallFreeValues ctorCallFreeRules ctorCallFreeOps vyperTypeContract context exprLowering emitHelper
  ctorCallFreeMemory loweringShapeDefs compileEnv venomInst list pair

Theorem runtime_default_store_memory_opcodes:
  (!opc. MEM opc [MLOAD; MSTORE; NOT; ADD; AND; MCOPY; ASSIGN;
    JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT] ==> P opc) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_memory ce src dst dt st s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      outcomes_free_copy_memory, outcomes_free_bytestring_copy,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] (cj 1 typed_copy_opcodes)]
QED

Theorem runtime_default_slot_copy_to_memory[local]:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_storage_to_memory src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_transient_to_memory src dst n s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_storage_to_memory_def, compile_transient_to_memory_def,
       compile_word_copy_loop_def, compile_word_copy_loop_op_def] >>
  conj_tac >> irule outcomes_free_word_copy_base >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, compile_ptr_store_def,
       outcomes_free_ptr_load, opcode_every_emit_void]
QED

Theorem runtime_default_ensure_memory_opcodes[local]:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc bytes words ctor imm s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `loc` >> simp[compile_ensure_in_memory_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst, outcomes_free_alloc_buffer,
      outcomes_free_imm_copy,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_slot_copy_to_memory]),
    gen_tac, strip_tac, irule every_state_insts_bind, irule every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> gvs[]
QED

Theorem runtime_default_unwrap_opcodes:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value cenv vv s)))
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def, every_state_insts_return] >>
  IF_CASES_TAC >- simp[outcomes_free_ptr_load] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[every_state_insts_return, runtime_default_ensure_memory_opcodes]
QED

Theorem runtime_default_binop_opcodes:
  (!opc. MEM opc [ADD; SUB; MUL; SDIV; Div; SMOD; Mod; EQ; ISZERO; OR; NOT;
    AND; ASSERT; SLT; SGT; GT; LT; Exp; XOR; SHL; SAR; SHR] ==> P opc) /\
  constant_binop bop /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_binop bop x y ty base_literal exp_literal s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `bop` >> fs[constant_binop_def, compile_binop_def, compile_compare_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
    opcode_every_emit_void, opcode_every_emit_inst, outcomes_free_compile_select,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_add_sub,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_mul,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_div_mod,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_pow]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem runtime_default_acc_opcodes:
  P BALANCE /\ P CODESIZE /\ P EXTCODEHASH /\ P EXTCODESIZE /\ P GT /\
  accessor <> Code /\
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (lower_value cfn cenv (BaseT AddressT) addr_e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_acc cfn cenv addr_e accessor s)))
Proof
  strip_tac >> Cases_on `accessor` >> fs[compile_acc_def] >>
  rpt (COND_CASES_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[opcode_every_emit_op, SND]
QED

Theorem runtime_default_type_builtin_opcodes:
  P ALLOCA /\ P ADD /\ P MSTORE /\ constant_type_builtin tb /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args s)))
Proof
  strip_tac >> Cases_on `tb` >> fs[constant_type_builtin_def,
    compile_type_builtin_dispatch_body_def, LET_THM] >>
  TRY (Cases_on `type_bounds rt` >> simp[]) >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >> gvs[] >>
  metis_tac[outcomes_free_builtin_empty_complex, SND]
QED

Theorem runtime_default_make_tuple_opcodes:
  !es tys buf off s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_tuple f ce es tys buf off s)))
Proof
  rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  irule make_tuple_opcode_bound >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_unwrap_opcodes,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_store_memory_opcodes]
QED

Theorem runtime_default_make_array_elems_opcodes:
  !es ety sz lw buf idx s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_array_elems f ce es ety sz lw buf idx s)))
Proof
  rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  irule make_array_elems_opcode_bound >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_unwrap_opcodes,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_store_memory_opcodes]
QED

Theorem runtime_default_make_array_opcodes:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_array f ce es ety sz lw buf s)))
Proof
  strip_tac >> simp[compile_make_array_def] >>
  irule every_state_insts_ignore_bind >> conj_tac
  >- (Cases_on `lw` >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
          opcode_every_emit_inst]) >>
  rpt strip_tac >> simp[runtime_default_make_array_elems_opcodes]
QED

Theorem runtime_default_struct_lit_opcodes:
  !fields buf off s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!nm e ty st. MEM (nm,e) fields /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_struct_lit f ce ty fields buf off s)))
Proof
  rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  irule struct_lit_opcode_bound >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_unwrap_opcodes,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_store_memory_opcodes] >>
  first_assum ACCEPT_TAC
QED

Theorem runtime_default_ifexp_arm_opcodes:
  EVERY P [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; MSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ifexp_arm ce rt at vv s)))
Proof
  simp[] >> strip_tac >> simp[compile_ifexp_arm_def] >>
  IF_CASES_TAC >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[every_state_insts_return, outcomes_free_alloc_buffer,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_unwrap_opcodes,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] runtime_default_store_memory_opcodes]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED
