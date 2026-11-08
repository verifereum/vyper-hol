Theory bodyPtrBytestringBuiltinsOpcodeSimple
Ancestors bodyPtrBytestringBuiltinsOpcodeArithmetic
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState
          builtinMath builtinMisc builtinSimple builtinStrings exprLowering

Theorem no_extcode_addmod:
  !a b c s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_addmod a b c s))
Proof
  rpt strip_tac >> simp[compile_addmod_def] >>
  irule no_extcode_ignore_bind >> simp[no_extcode_emit_void, no_extcode_emit_op]
QED

Theorem no_extcode_mulmod:
  !a b c s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_mulmod a b c s))
Proof
  rpt strip_tac >> simp[compile_mulmod_def] >>
  irule no_extcode_ignore_bind >> simp[no_extcode_emit_void, no_extcode_emit_op]
QED

Theorem no_extcode_pow_mod256:
  !a b s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_pow_mod256 a b s))
Proof simp[compile_pow_mod256_def, no_extcode_emit_op]
QED

Theorem no_extcode_builtin_abs:
  !v s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_builtin_abs v s))
Proof
  rpt strip_tac >> simp[compile_builtin_abs_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_select])
QED

Theorem no_extcode_ecrecover:
  !h v r ss s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_ecrecover h v r ss s))
Proof
  rpt strip_tac >> simp[compile_ecrecover_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_alloc_buffer])
QED

Theorem no_extcode_ecadd_points:
  !p q s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_ecadd_points p q s))
Proof
  rpt strip_tac >> simp[compile_ecadd_points_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_alloc_buffer])
QED

Theorem no_extcode_ecmul_point:
  !p n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_ecmul_point p n s))
Proof
  rpt strip_tac >> simp[compile_ecmul_point_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_alloc_buffer])
QED

Theorem no_extcode_blockhash:
  !n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_blockhash n s))
Proof
  rpt strip_tac >> simp[compile_blockhash_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_blobhash:
  !n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_blobhash n s))
Proof simp[compile_blobhash_def, no_extcode_emit_op]
QED

Theorem no_extcode_as_wei_value_int:
  !v sc b s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_as_wei_value_int v sc b s))
Proof
  rpt strip_tac >> simp[compile_as_wei_value_int_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_select])
QED

Theorem no_extcode_as_wei_value_decimal:
  !v sc d s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_as_wei_value_decimal v sc d s))
Proof
  rpt strip_tac >> simp[compile_as_wei_value_decimal_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_select])
QED

Theorem no_extcode_uint2str:
  !v digits sz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_uint2str v digits sz s))
Proof
  rpt strip_tac >> simp[compile_uint2str_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_inst, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_new_block, no_extcode_alloc_buffer, no_extcode_fresh_ops])
QED
