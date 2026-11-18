Theory deployOutcomesFreeBuiltinGenerators
Ancestors
  ctorCallFreeRules
  deployOutcomesFreeGenerators builtinMisc builtinStrings builtinHashing
  builtinBytes builtinMath builtinSimple exprLowering context emitHelper
  compileEnv venomInst list pair
  ctorCallFreeOps ctorCallFreeValues

(* The implementation boundary is monadic preservation of the instruction
   inventory. This tactic only decomposes binds and their finite branches. *)
val builtin_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    outcomes_free_alloc_buffer, every_state_insts_fresh_id, every_state_insts_fresh_var,
        every_state_insts_fresh_label, every_state_insts_new_block,
    outcomes_free_ptr_load]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
    irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_compile_uint2str:
  (!opc. MEM opc [ALLOCA; ASSIGN; JMP; EQ; JNZ; Mod; ADD; SUB; MSTORE; Div] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_uint2str v n sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_uint2str_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_builtin_len:
  (!opc. MEM opc [ADD; ILOAD; DLOAD; MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_len ctor imm v loc s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_builtin_len_def, outcomes_free_ptr_load]
QED

Theorem outcomes_free_compile_assert_slice_bounds:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_assert_slice_bounds a b c s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_assert_slice_bounds_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_bytestring_src:
  P MLOAD /\ P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytestring_src a s)))
Proof
  strip_tac >> simp[compile_bytestring_src_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_slice_out_buf:
  P ALLOCA /\ P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_out_buf sz s)))
Proof
  strip_tac >> simp[compile_slice_out_buf_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_slice_data:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; MCOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_data a b c d sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_data_def, compile_assert_slice_bounds_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_slice_calldata:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; CALLDATASIZE; CALLDATACOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_calldata a b sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_calldata_def, compile_slice_out_buf_def, compile_assert_slice_bounds_def] >>
  builtin_preserve_tac >> pairarg_tac >> gvs[] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_slice_code:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; CODESIZE; CODECOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_code a b sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_code_def, compile_slice_out_buf_def, compile_assert_slice_bounds_def] >>
  builtin_preserve_tac >> pairarg_tac >> gvs[] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_slice_extcode:
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; EXTCODESIZE; EXTCODECOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_extcode a b c sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_extcode_def, compile_assert_slice_bounds_def,
    compile_slice_out_buf_def] >> builtin_preserve_tac >>
  pairarg_tac >> gvs[] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_keccak256_word:
  P ALLOCA /\ P MSTORE /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_word v s)))
Proof
  strip_tac >> simp[compile_keccak256_word_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_keccak256_bytesm:
  P ALLOCA /\ P MSTORE /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_bytesm v n s)))
Proof
  strip_tac >> simp[compile_keccak256_bytesm_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_keccak256_bytes:
  P MLOAD /\ P ADD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_keccak256_bytes v s)))
Proof
  strip_tac >> simp[compile_keccak256_bytes_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_bytestring_hash:
  P MLOAD /\ P ADD /\ P SHA3 /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytestring_hash v s)))
Proof
  strip_tac >> simp[compile_bytestring_hash_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_method_id_hash:
  (!opc. MEM opc [ALLOCA; MSTORE; SHA3; MLOAD; ADD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_method_id_hash ty v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `ty` >> simp[compile_method_id_hash_def, outcomes_free_compile_keccak256_bytes] >>
  Cases_on `b` >> simp[compile_method_id_hash_def, outcomes_free_compile_keccak256_bytes] >>
  Cases_on `b'` >> simp[compile_method_id_hash_def, outcomes_free_compile_keccak256_bytes,
    outcomes_free_compile_keccak256_bytesm]
QED

Theorem outcomes_free_compile_method_id_runtime:
  (!opc. MEM opc [ALLOCA; MSTORE; SHA3; MLOAD; ADD; SHR; SHL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_method_id_runtime ty v is_bytes4 s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_method_id_runtime_def] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_method_id_hash] >>
  rpt strip_tac >> builtin_preserve_tac
QED

Theorem outcomes_free_emit_membership_eqs:
  !elems s. P EQ /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (emit_membership_eqs needle elems s)))
Proof
  Induct_on `elems` >> rpt strip_tac >> simp[emit_membership_eqs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_fold_membership_or:
  !cs acc s. P OR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (fold_membership_or acc cs s)))
Proof
  Induct_on `cs` >> rpt strip_tac >> simp[fold_membership_or_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_fold_membership_and:
  !cs acc s. P ISZERO /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (fold_membership_and acc cs s)))
Proof
  Induct_on `cs` >> rpt strip_tac >> simp[fold_membership_and_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_compile_list_membership_in:
  P EQ /\ P OR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_in needle elems s)))
Proof
  strip_tac >> simp[compile_list_membership_in_def] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[outcomes_free_emit_membership_eqs] >> rpt strip_tac >>
  Cases_on `x` >> simp[every_state_insts_return, outcomes_free_fold_membership_or]
QED

Theorem outcomes_free_compile_list_membership_notin:
  P EQ /\ P ISZERO /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_notin needle elems s)))
Proof
  strip_tac >> simp[compile_list_membership_notin_def] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[outcomes_free_emit_membership_eqs] >> rpt strip_tac >>
  Cases_on `x` >> simp[every_state_insts_return] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      outcomes_free_fold_membership_and]
QED

Theorem outcomes_free_compile_array_membership_loop:
  (!opc. MEM opc [JMP; ASSIGN; GT; ISZERO; ASSERT; EQ; JNZ; MUL; ADD] ==> P opc) /\
  (!addr st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (loader addr st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_array_membership_loop needle arr len sz off loader bound is_in s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `bound` >> simp[compile_array_membership_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
      every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
          every_state_insts_new_block]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC, first_assum irule])
QED

Theorem outcomes_free_compile_var_array_membership:
  (!opc. MEM opc [JMP; ASSIGN; GT; ISZERO; ASSERT; EQ; JNZ; MUL; ADD;
    ILOAD; DLOAD; MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_var_array_membership ce needle arr ty is_in s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_var_array_membership_def] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule (SRULE [DISJ_IMP_THM, FORALL_AND_THM]
        outcomes_free_compile_array_membership_loop) >> simp[outcomes_free_ptr_load]) >>
  Cases_on `ty` >> simp[every_state_insts_return] >>
  Cases_on `b` >> simp[every_state_insts_return, outcomes_free_ptr_load]
QED

(* Name fast paths pair name lookup with unwrapping. *)
Theorem outcomes_free_name_unwrap:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (unwrap_value ce (FST (compile_name_vv ce ty id s))
       (SND (compile_name_vv ce ty id s)))))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  irule (SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value) >> simp[] >>
  simp[compile_name_vv_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[every_state_insts_return]) >>
  irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst, every_state_insts_return]
QED

Theorem outcomes_free_compile_addmod_names:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; ASSERT; ADDMOD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_addmod_names ce rt aty a bty b mty m s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_addmod_names_def, ELIM_UNCURRY, exprBopLoweringTheory.as_stack_val_pair,
    outcomes_free_compile_addmod,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_name_unwrap]
QED

Theorem outcomes_free_compile_mulmod_names:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; ASSERT; MULMOD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_mulmod_names ce rt aty a bty b mty m s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_mulmod_names_def, ELIM_UNCURRY, exprBopLoweringTheory.as_stack_val_pair,
    outcomes_free_compile_mulmod,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_name_unwrap]
QED

Theorem outcomes_free_compile_powmod256_names:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; Exp] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_powmod256_names ce rt aty a bty b s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_powmod256_names_def, ELIM_UNCURRY, exprBopLoweringTheory.as_stack_val_pair,
    outcomes_free_compile_pow_mod256,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_name_unwrap]
QED
