(* Safe, callback-free arithmetic operation boundaries. *)
Theory ctorCallFreeOps
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper exprLowering
  builtinSimple builtinMath builtinMisc ctorCallFreeRules

Theorem call_free_select:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_select cond_op yes_op no_op st)))
Proof
  qid_spec_tac `st` >> simp[compile_select_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op])])
QED

Theorem call_free_builtin_abs:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_builtin_abs v st)))
Proof
  qid_spec_tac `st` >> simp[compile_builtin_abs_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
                              call_free_select])])
QED

Theorem call_free_env_var:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_env_var item st)))
Proof
  Cases_on `item` >> qid_spec_tac `st` >> simp[compile_env_var_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op])])
QED

Theorem call_free_compare:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_compare bop x y ty st)))
Proof
  Cases_on `bop` >> Cases_on `is_uint256 ty` >> qid_spec_tac `st` >>
  simp[compile_compare_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_inst,
                              every_state_insts_return])])
QED

Theorem call_free_wrap_truncate:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (wrap_truncate v ty st)))
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, call_free_emit_op, every_state_insts_return]
QED

Theorem call_free_invert:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_invert v ty ce st)))
Proof
  Cases_on `ty` >> simp[compile_invert_def, call_free_emit_op]
QED

Theorem call_free_neg:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_neg v ty st)))
Proof
  Cases_on `type_bounds ty` >>
  simp[compile_neg_def, every_state_insts_bind,
    every_state_insts_ignore_bind, call_free_emit_op, call_free_emit_void]
QED

Theorem call_free_clamp:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_clamp v ty st)))
Proof
  Cases_on `type_bounds ty` >> Cases_on `is_signed_type ty` >>
  qid_spec_tac `st` >> simp[compile_clamp_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_clamp_and_return:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (clamp_and_return v ty st)))
Proof
  simp[clamp_and_return_def, every_state_insts_ignore_bind,
       call_free_clamp, every_state_insts_return]
QED

Theorem call_free_mul_overflow_check:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_mul_overflow_check x y v signed bits st)))
Proof
  Cases_on `signed` >> Cases_on `bits = 256` >> qid_spec_tac `st` >>
  simp[compile_mul_overflow_check_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
                              every_state_insts_return])])
QED

Theorem call_free_safe_arithmetic:
  (!x y ty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_safe_add x y ty st)))) /\
  (!x y ty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_safe_sub x y ty st)))) /\
  (!x y ty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_safe_mul x y ty st)))) /\
  (!x y ty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_safe_div x y ty st)))) /\
  (!x y divisor ty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_safe_decimal_div x y divisor ty st)))) /\
  (!x y ty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_safe_mod x y ty st))))
Proof
  rpt conj_tac >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_safe_add_def, compile_safe_sub_def, compile_safe_mul_def,
       compile_safe_div_def, compile_safe_decimal_div_def, compile_safe_mod_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_clamp_and_return, call_free_mul_overflow_check,
      every_state_insts_return]),
    IF_CASES_TAC >> simp[], gen_tac])
QED

Theorem call_free_safe_pow:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_safe_pow x y ty bl el st)))
Proof
  Cases_on `bl` >> Cases_on `el` >> Cases_on `is_signed_type ty` >>
  qid_spec_tac `st` >> simp[compile_safe_pow_def] >> rpt IF_CASES_TAC >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_clamp, every_state_insts_return])])
QED

Theorem call_free_binop:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_binop bop x y ty bl el st)))
Proof
  Cases_on `bop` >> qid_spec_tac `st` >> simp[compile_binop_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_inst,
      call_free_safe_arithmetic, call_free_safe_pow, call_free_compare,
      call_free_wrap_truncate, call_free_select, every_state_insts_return]),
    IF_CASES_TAC >> simp[], gen_tac])
QED

Theorem call_free_int_clamp[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_int_clamp signed bits v st)))
Proof
  Cases_on `signed` >> qid_spec_tac `st` >> simp[compile_int_clamp_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
                              every_state_insts_return])])
QED

Theorem call_free_load_bytestring_as_word[local]:
  opc <> RETURNDATACOPY /\ opc <> INVOKE ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (load_bytestring_as_word v opc st)))
Proof
  strip_tac >> Cases_on `opc = SAR` >> simp[load_bytestring_as_word_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])])
QED

Theorem call_free_type_convert:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_type_convert v cop st)))
Proof
  Cases_on `cop` >> qid_spec_tac `st` >> simp[compile_type_convert_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_int_clamp, call_free_load_bytestring_as_word,
      every_state_insts_return]),
    IF_CASES_TAC >> simp[], gen_tac,
    pairarg_tac >> gvs[] >> qid_spec_tac `st`])
QED

Theorem call_free_modular:
  (!a b c st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_addmod a b c st)))) /\
  (!a b c st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_mulmod a b c st)))) /\
  (!a b st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_pow_mod256 a b st))))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_addmod_def, compile_mulmod_def, compile_pow_mod256_def,
    every_state_insts_ignore_bind, call_free_emit_void, call_free_emit_op]
QED

Theorem call_free_blockhash:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_blockhash v st)))
Proof
  qid_spec_tac `st` >> simp[compile_blockhash_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_blobhash:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_blobhash v st)))
Proof
  simp[compile_blobhash_def, call_free_emit_op]
QED

Theorem call_free_rounding:
  (!v divisor st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_floor v divisor st)))) /\
  (!v divisor st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_ceil v divisor st))))
Proof
  conj_tac >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_floor_def, compile_ceil_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_select])])
QED

Theorem call_free_as_wei_value:
  (!v scale signed st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_as_wei_value_int v scale signed st)))) /\
  (!v scale divisor st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_as_wei_value_decimal v scale divisor st))))
Proof
  conj_tac >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_as_wei_value_int_def, compile_as_wei_value_decimal_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      every_state_insts_return]), IF_CASES_TAC >> simp[], gen_tac])
QED

Theorem call_free_clamp_basetype:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_clamp_basetype v ty st)))
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, every_state_insts_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, every_state_insts_return] >>
  FIRST [rename1 `compile_clamp_basetype v (BaseT (BytesT bd))` >>
         Cases_on `bd` >> simp[compile_clamp_basetype_def, every_state_insts_return],
         all_tac] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_clamp_and_return, every_state_insts_return]),
    IF_CASES_TAC >> simp[], gen_tac])
QED

Theorem call_free_calldatasize:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_builtin_calldatasize st)))
Proof
  simp[compile_builtin_calldatasize_def, call_free_emit_op]
QED
