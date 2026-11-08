Theory bodyPtrBytestringBuiltinsSubscriptAllocationTrace
Ancestors bodyPtrBytestringBuiltinsChildAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace exprLowering context compileEnv emitHelper

Theorem compile_mapping_subscript_allocation_trace[simp]:
  !base key s. allocation_trace s (SND (compile_mapping_subscript base key s))
Proof
  rpt gen_tac >> simp[compile_mapping_subscript_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_keccak256_key_allocation_trace[simp]:
  !key b s. allocation_trace s (SND (compile_keccak256_key key b s))
Proof
  rpt gen_tac >> Cases_on `b` >> simp[compile_keccak256_key_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_tuple_subscript_allocation_trace[simp]:
  !base off s. allocation_trace s (SND (compile_tuple_subscript base off s))
Proof
  simp[compile_tuple_subscript_def]
QED

Theorem compile_array_subscript_allocation_trace:
  !base idx dyn count scale sz signed loader.
  (!s. allocation_trace s (SND (loader base s))) ==>
  !s. allocation_trace s
    (SND (compile_array_subscript base idx dyn count scale sz signed loader s))
Proof
  rpt strip_tac >> Cases_on `dyn` >> Cases_on `signed` >>
  simp[compile_array_subscript_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_subscript_allocation_trace:
  !cfn cenv rt ty base idx.
  (!ce t e s. (e = base \/ e = idx) ==>
    allocation_trace s (SND (cfn ce t e s))) ==>
  !s. allocation_trace s (SND (compile_subscript cfn cenv rt ty base idx s))
Proof
  map_every qx_gen_tac [`cfn`, `cenv`, `rt`, `ty`, `be`, `idx`] >>
  rpt strip_tac >> simp[compile_subscript_def] >>
  irule allocation_trace_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> simp[] >> Cases_on `place_type cenv be` >> simp[] >>
  TRY (rename1 `ValPT vt` >> Cases_on `vt` >> simp[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC,
              irule lower_value_child_allocation_trace,
              irule compile_array_subscript_allocation_trace] >> simp[])
QED
