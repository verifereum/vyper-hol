(* Safe, callback-free arithmetic operation boundaries. *)
Theory ctorCallFreeOps
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper exprLowering
  builtinSimple builtinMath builtinMisc ctorCallFreeRules

Theorem outcomes_free_clamp:
  (!opc. MEM opc [SLT; SGT; ISZERO; AND; GT; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_clamp v ty s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (clamp_and_return v ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `type_bounds ty` >> simp[clamp_and_return_def, compile_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
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
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
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
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_safe_mul:
  (!opc. MEM opc [MUL; SDIV; Div; EQ; ISZERO; OR; NOT; AND; ASSERT; SLT; SGT; GT]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_safe_mul x y ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_safe_mul_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_mul_check]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
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
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
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
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_clamp]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_compare:
  (!opc. MEM opc [SLT; SGT; LT; GT; EQ; ISZERO; INVALID] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_compare bop x y ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `bop` >> simp[compile_compare_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_wrap_truncate:
  P SIGNEXTEND /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (wrap_truncate res ty s)))
Proof
  strip_tac >> simp[wrap_truncate_def] >>
  rpt IF_CASES_TAC >> simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return]
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
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    outcomes_free_wrap_truncate,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_add_sub,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_mul,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_div_mod,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_safe_pow,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_compare]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

(* Steps through emit/return/fresh/bind boundaries of a generator body. *)
val opcode_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
    opcode_every_emit_inst, every_state_insts_return, every_state_insts_fresh_id,
    every_state_insts_fresh_var, every_state_insts_fresh_label,
    every_state_insts_new_block]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_int_clamp:
  (!opc. MEM opc [SLT; SGT; GT; ISZERO; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_int_clamp sg bits v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_int_clamp_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_load_bytestring_as_word:
  (!opc. MEM opc [MLOAD; ADD; ISZERO; MUL; SUB; shift] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (load_bytestring_as_word v shift s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[load_bytestring_as_word_def] >> opcode_preserve_tac
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
    CHANGED_TAC opcode_preserve_tac, pairarg_tac])
QED

Theorem outcomes_free_clamp_basetype:
  (!opc. MEM opc [SHL; SLT; SGT; GT; ISZERO; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_clamp_basetype v ty s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `ty` >> simp[compile_clamp_basetype_def, every_state_insts_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[compile_clamp_basetype_def,
    every_state_insts_return, outcomes_free_clamp, DISJ_IMP_THM, FORALL_AND_THM]),
    CHANGED_TAC opcode_preserve_tac, rename1 `BytesT bd` >> Cases_on `bd`])
QED

Theorem outcomes_free_compile_select:
  P XOR /\ P MUL /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_select c a b s)))
Proof
  strip_tac >> simp[compile_select_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_neg:
  P SGT /\ P ASSERT /\ P SUB /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_neg v ty s)))
Proof
  strip_tac >> simp[compile_neg_def] >> pairarg_tac >> simp[] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_builtin_abs:
  (!opc. MEM opc [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_abs v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_builtin_abs_def, compile_select_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_blockhash:
  (!opc. MEM opc [NUMBER; SUB; SLT; ISZERO; ASSERT; LT; BLOCKHASH] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_blockhash v s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_blockhash_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_blobhash:
  P BLOBHASH /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_blobhash v s)))
Proof
  simp[compile_blobhash_def, opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_floor:
  (!opc. MEM opc [SLT; SUB; XOR; MUL; SDIV] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_floor v d s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_floor_def, compile_select_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_ceil:
  (!opc. MEM opc [SLT; ADD; XOR; MUL; SDIV] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ceil v d s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_ceil_def, compile_select_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_env_var:
  (!opc. MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; SUB; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS] ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_env_var e s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >> Cases_on `e` >>
  simp[compile_env_var_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_builtin_calldatasize:
  P CALLDATASIZE /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_builtin_calldatasize s)))
Proof
  simp[compile_builtin_calldatasize_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_invert:
  P XOR /\ P NOT /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_invert v ty ce s)))
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_invert_def, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_as_wei_value_int:
  (!opc. MEM opc [MUL; Div; EQ; ISZERO; OR; SLT; AND; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_as_wei_value_int v scale signed s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_as_wei_value_int_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_as_wei_value_decimal:
  (!opc. MEM opc [SLT; ISZERO; ASSERT; Div; MUL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_as_wei_value_decimal v scale d s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_as_wei_value_decimal_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_pow_mod256:
  P Exp /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_pow_mod256 a b s)))
Proof
  simp[compile_pow_mod256_def, opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_addmod:
  P ASSERT /\ P ADDMOD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_addmod a b c s)))
Proof
  strip_tac >> simp[compile_addmod_def] >> opcode_preserve_tac
QED

Theorem outcomes_free_compile_mulmod:
  P ASSERT /\ P MULMOD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_mulmod a b c s)))
Proof
  strip_tac >> simp[compile_mulmod_def] >> opcode_preserve_tac
QED

Theorem opcode_every_select:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_select cond_op yes_op no_op st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_select >> simp[]
QED

Theorem opcode_every_builtin_abs:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_abs v st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_builtin_abs >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_env_var:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_env_var item st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_env_var >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_compare:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_compare bop x y ty st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compare >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_wrap_truncate:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (wrap_truncate v ty st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_wrap_truncate >> simp[]
QED

Theorem opcode_every_invert:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_invert v ty ce st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_invert >> simp[]
QED

Theorem opcode_every_neg:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_neg v ty st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_neg >> simp[]
QED

Theorem opcode_every_clamp:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_clamp v ty st)))
  )
Proof
  rpt strip_tac >> irule (cj 1 outcomes_free_clamp) >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_clamp_and_return:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (clamp_and_return v ty st)))
  )
Proof
  rpt strip_tac >> irule (cj 2 outcomes_free_clamp) >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_mul_overflow_check:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_mul_overflow_check x y v signed bits st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_mul_check >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_safe_arithmetic:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!x y ty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_safe_add x y ty st)))) /\
  (!x y ty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_safe_sub x y ty st)))) /\
  (!x y ty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_safe_mul x y ty st)))) /\
  (!x y ty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_safe_div x y ty st)))) /\
  (!x y divisor ty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_safe_decimal_div x y divisor ty st)))) /\
  (!x y ty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_safe_mod x y ty st))))
  )
Proof
  strip_tac >> rpt conj_tac >> rpt strip_tac >|
  [irule (cj 1 outcomes_free_safe_add_sub), irule (cj 2 outcomes_free_safe_add_sub),
   irule outcomes_free_safe_mul, irule (cj 1 outcomes_free_safe_div_mod),
   irule (cj 2 outcomes_free_safe_div_mod), irule (cj 3 outcomes_free_safe_div_mod)] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_safe_pow:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_safe_pow x y ty bl el st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_safe_pow >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_binop:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_binop bop x y ty bl el st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_binop >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_type_convert:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_type_convert v cop st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_type_convert >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_modular:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!a b c st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_addmod a b c st)))) /\
  (!a b c st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_mulmod a b c st)))) /\
  (!a b st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_pow_mod256 a b st))))
  )
Proof
  strip_tac >> rpt conj_tac >> rpt strip_tac >|
  [irule outcomes_free_compile_addmod, irule outcomes_free_compile_mulmod,
   irule outcomes_free_compile_pow_mod256] >> simp[]
QED

Theorem opcode_every_blockhash:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_blockhash v st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_blockhash >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_blobhash:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_blobhash v st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_blobhash >> simp[]
QED

Theorem opcode_every_rounding:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!v divisor st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_floor v divisor st)))) /\
  (!v divisor st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ceil v divisor st))))
  )
Proof
  strip_tac >> rpt conj_tac >> rpt strip_tac >|
  [irule outcomes_free_compile_floor, irule outcomes_free_compile_ceil] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_as_wei_value:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!v scale signed st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_as_wei_value_int v scale signed st)))) /\
  (!v scale divisor st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_as_wei_value_decimal v scale divisor st))))
  )
Proof
  strip_tac >> rpt conj_tac >> rpt strip_tac >|
  [irule outcomes_free_compile_as_wei_value_int,
   irule outcomes_free_compile_as_wei_value_decimal] >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_clamp_basetype:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_clamp_basetype v ty st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_clamp_basetype >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_calldatasize:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_calldatasize st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_builtin_calldatasize >> simp[]
QED
