Theory bodyPtrBytestringBuiltinsStringAllocationTrace
Ancestors bodyPtrBytestringBuiltinsBytesAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace builtinStrings exprLowering

Theorem compile_uint2str_allocation_trace[simp]:
  !v digits sz s. allocation_trace s (SND (compile_uint2str v digits sz s))
Proof
  rpt gen_tac >> simp[compile_uint2str_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_concat_allocation_trace:
  !cfn ce es data infos off s.
  (!e s0. MEM e es ==> allocation_trace s0 (SND (cfn ce (expr_type e) e s0))) ==>
  allocation_trace s (SND (compile_concat cfn ce es data infos off s))
Proof
  map_every qx_gen_tac [`cfn`, `ce`] >> Induct_on `es` >>
  rpt gen_tac >> strip_tac >> simp[compile_concat_def] >>
  Cases_on `infos` >> simp[compile_concat_def] >>
  PairCases_on `h'` >> simp[compile_concat_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC,
              irule lower_value_child_allocation_trace] >> simp[]) >>
  first_x_assum irule >> simp[]
QED
