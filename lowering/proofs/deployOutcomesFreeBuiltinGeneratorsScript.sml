Theory deployOutcomesFreeBuiltinGenerators
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeGenerators builtinMisc builtinStrings builtinHashing
  builtinBytes builtinMath builtinSimple exprLowering context emitHelper
  compileEnv venomInst list pair

(* The implementation boundary is monadic preservation of the instruction
   inventory. This tactic only decomposes binds and their finite branches. *)
val builtin_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_alloc_buffer, outcomes_free_fresh, outcomes_free_new_block,
    outcomes_free_ptr_load]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_compile_select:
  P XOR /\ P MUL /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_select c a b s)))
Proof
  strip_tac >> simp[compile_select_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_neg:
  P SGT /\ P ASSERT /\ P SUB /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_neg v ty s)))
Proof
  strip_tac >> simp[compile_neg_def] >> pairarg_tac >> simp[] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_builtin_abs:
  (!opc. MEM opc [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_abs v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_builtin_abs_def, compile_select_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_blockhash:
  (!opc. MEM opc [NUMBER; SUB; SLT; ISZERO; ASSERT; LT; BLOCKHASH] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_blockhash v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_blockhash_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_blobhash:
  P BLOBHASH /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_blobhash v s)))
Proof
  simp[compile_blobhash_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_compile_floor:
  (!opc. MEM opc [SLT; SUB; XOR; MUL; SDIV] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_floor v d s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_floor_def, compile_select_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_ceil:
  (!opc. MEM opc [SLT; ADD; XOR; MUL; SDIV] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ceil v d s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_ceil_def, compile_select_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_uint2str:
  (!opc. MEM opc [ALLOCA; ASSIGN; JMP; EQ; JNZ; Mod; ADD; SUB; MSTORE; Div] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_uint2str v n sz s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_uint2str_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_env_var:
  (!opc. MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; SUB; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS] ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_env_var e s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >> Cases_on `e` >>
  simp[compile_env_var_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_builtin_calldatasize:
  P CALLDATASIZE /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_calldatasize s)))
Proof
  simp[compile_builtin_calldatasize_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_compile_invert:
  P XOR /\ P NOT /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_invert v ty ce s)))
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_invert_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_compile_builtin_len:
  (!opc. MEM opc [ADD; ILOAD; DLOAD; MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_len ctor imm v loc s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_builtin_len_def, outcomes_free_ptr_load]
QED

Theorem outcomes_free_compile_as_wei_value_int:
  (!opc. MEM opc [MUL; Div; EQ; ISZERO; OR; SLT; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_as_wei_value_int v scale signed s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_as_wei_value_int_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_as_wei_value_decimal:
  (!opc. MEM opc [SLT; ISZERO; ASSERT; Div; MUL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_as_wei_value_decimal v scale d s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_as_wei_value_decimal_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_pow_mod256:
  P Exp /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_pow_mod256 a b s)))
Proof
  simp[compile_pow_mod256_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_compile_addmod:
  P ASSERT /\ P ADDMOD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_addmod a b c s)))
Proof
  strip_tac >> simp[compile_addmod_def] >> builtin_preserve_tac
QED

Theorem outcomes_free_compile_mulmod:
  P ASSERT /\ P MULMOD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_mulmod a b c s)))
Proof
  strip_tac >> simp[compile_mulmod_def] >> builtin_preserve_tac
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
  (!opc. MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT; EXTCODESIZE; EXTCODECOPY; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slice_extcode a b c buf dat s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slice_extcode_def, compile_assert_slice_bounds_def] >> builtin_preserve_tac
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
  simp[compile_method_id_runtime_def] >> irule outcomes_free_bind >>
  simp[SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compile_method_id_hash] >>
  rpt strip_tac >> builtin_preserve_tac
QED

Theorem outcomes_free_emit_membership_eqs:
  !elems s. P EQ /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (emit_membership_eqs needle elems s)))
Proof
  Induct_on `elems` >> rpt strip_tac >> simp[emit_membership_eqs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_fold_membership_or:
  !cs acc s. P OR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (fold_membership_or acc cs s)))
Proof
  Induct_on `cs` >> rpt strip_tac >> simp[fold_membership_or_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_fold_membership_and:
  !cs acc s. P ISZERO /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (fold_membership_and acc cs s)))
Proof
  Induct_on `cs` >> rpt strip_tac >> simp[fold_membership_and_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_compile_list_membership_in:
  P EQ /\ P OR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_in needle elems s)))
Proof
  strip_tac >> simp[compile_list_membership_in_def] >> irule outcomes_free_bind >>
  simp[outcomes_free_emit_membership_eqs] >> rpt strip_tac >>
  Cases_on `x` >> simp[outcomes_free_return, outcomes_free_fold_membership_or]
QED

Theorem outcomes_free_compile_list_membership_notin:
  P EQ /\ P ISZERO /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_notin needle elems s)))
Proof
  strip_tac >> simp[compile_list_membership_notin_def] >> irule outcomes_free_bind >>
  simp[outcomes_free_emit_membership_eqs] >> rpt strip_tac >>
  Cases_on `x` >> simp[outcomes_free_return] >> irule outcomes_free_bind >>
  simp[outcomes_free_emit_ops, outcomes_free_fold_membership_and]
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
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
      outcomes_free_fresh, outcomes_free_new_block]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
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
  simp[compile_var_array_membership_def] >> irule outcomes_free_bind >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule (SRULE [DISJ_IMP_THM, FORALL_AND_THM]
        outcomes_free_compile_array_membership_loop) >> simp[outcomes_free_ptr_load]) >>
  Cases_on `ty` >> simp[outcomes_free_return] >>
  Cases_on `b` >> simp[outcomes_free_return, outcomes_free_ptr_load]
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
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[outcomes_free_return]) >>
  irule outcomes_free_ignore_bind >> simp[outcomes_free_emit_ops, outcomes_free_return]
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
  simp[compile_addmod_names_def, ELIM_UNCURRY, outcomes_free_as_stack_val,
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
  simp[compile_mulmod_names_def, ELIM_UNCURRY, outcomes_free_as_stack_val,
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
  simp[compile_powmod256_names_def, ELIM_UNCURRY, outcomes_free_as_stack_val,
    outcomes_free_compile_pow_mod256,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_name_unwrap]
QED
