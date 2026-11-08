Theory bodyPtrBytestringBuiltinsOperatorAllocationTrace
Ancestors bodyPtrBytestringBuiltinsArithmeticAllocationTrace
          bodyPtrBytestringBuiltinsSubscriptAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace exprLowering builtinSimple

Theorem compile_safe_pow_allocation_trace[simp]:
  !x y ty b e s. allocation_trace s (SND (compile_safe_pow x y ty b e s))
Proof
  rpt gen_tac >> Cases_on `b` >> Cases_on `e` >> simp[compile_safe_pow_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_compare_allocation_trace[simp]:
  !opr x y ty s. allocation_trace s (SND (compile_compare opr x y ty s))
Proof
  rpt gen_tac >> Cases_on `opr` >> simp[compile_compare_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem wrap_truncate_allocation_trace[simp]:
  !r ty s. allocation_trace s (SND (wrap_truncate r ty s))
Proof
  rpt gen_tac >> simp[wrap_truncate_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem compile_select_allocation_trace[simp]:
  !c x y s. allocation_trace s (SND (compile_select c x y s))
Proof
  rpt gen_tac >> simp[compile_select_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_binop_allocation_trace[simp]:
  !opr x y ty b e s. allocation_trace s (SND (compile_binop opr x y ty b e s))
Proof
  rpt gen_tac >> Cases_on `opr` >> simp[compile_binop_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_bytestring_hash_allocation_trace[simp]:
  !p s. allocation_trace s (SND (compile_bytestring_hash p s))
Proof
  rpt gen_tac >> simp[compile_bytestring_hash_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_list_membership_in_allocation_trace[simp]:
  !n es s. allocation_trace s (SND (compile_list_membership_in n es s))
Proof
  gen_tac >> Induct >> simp[compile_list_membership_in_def] >>
  Cases_on `es` >> simp[compile_list_membership_in_def] >> rpt gen_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_list_membership_notin_allocation_trace[simp]:
  !n es s. allocation_trace s (SND (compile_list_membership_notin n es s))
Proof
  gen_tac >> Induct >> simp[compile_list_membership_notin_def] >>
  Cases_on `es` >> simp[compile_list_membership_notin_def] >> rpt gen_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_array_membership_loop_allocation_trace:
  !n a len sz off loader is_in.
  (!op s. allocation_trace s (SND (loader op s))) ==>
  !s. allocation_trace s
    (SND (compile_array_membership_loop n a len sz off loader is_in s))
Proof
  rpt strip_tac >> simp[compile_array_membership_loop_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_var_array_membership_allocation_trace[simp]:
  !ce n vv ty b s.
    allocation_trace s (SND (compile_var_array_membership ce n vv ty b s))
Proof
  rpt gen_tac >> Cases_on `ty` >>
  TRY (rename1 `ArrayT et sz` >> Cases_on `sz`) >>
  simp[compile_var_array_membership_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind,
              irule compile_array_membership_loop_allocation_trace,
              IF_CASES_TAC] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_extcodesize_check_allocation_trace[simp]:
  !a s. allocation_trace s (SND (compile_extcodesize_check a s))
Proof
  rpt gen_tac >> simp[compile_extcodesize_check_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_return_value_decode_allocation_trace[simp]:
  !b lo hi s. allocation_trace s (SND (compile_return_value_decode b lo hi s))
Proof
  rpt gen_tac >> simp[compile_return_value_decode_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED
