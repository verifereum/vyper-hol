Theory bodyPtrBytestringBuiltinsCallStagingAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsStoreAllocationTrace
          bodyPtrBytestringBuiltinsAbiAllocationTrace
          bodyPtrBytestringBuiltinsOperatorAllocationTrace
          bodyPtrBytestringBuiltinsAssemblyAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace exprLowering context emitHelper

Theorem fresh_vars_allocation_trace[simp]:
  !n s. allocation_trace s (SND (fresh_vars n s))
Proof
  Induct >> simp[fresh_vars_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem emit_multi_op_allocation_trace[simp]:
  !opc args n s. opc <> ALLOCA ==>
    allocation_trace s (SND (emit_multi_op opc args n s))
Proof
  rpt strip_tac >> simp[emit_multi_op_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_alloc_dynamic_allocation_trace[simp]:
  !size s. allocation_trace s (SND (compile_alloc_dynamic size s))
Proof
  simp[compile_alloc_dynamic_def]
QED

Theorem compile_slot_to_memory_allocation_trace[simp]:
  !src dst n loc s. allocation_trace s (SND (compile_slot_to_memory src dst n loc s))
Proof
  simp[compile_slot_to_memory_def]
QED

Theorem compile_multi_vvs_allocation_trace:
  !cfn cenv. (!ce ty e s. allocation_trace s (SND (cfn ce ty e s))) ==>
  !es s. allocation_trace s (SND (compile_multi_vvs cfn cenv es s))
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[compile_multi_vvs_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem store_multi_results_allocation_trace[simp]:
  !buf vs off s. allocation_trace s (SND (store_multi_results buf vs off s))
Proof
  gen_tac >> Induct >> simp[store_multi_results_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_extcall_store_values_allocation_trace[simp]:
  !ce vs buf off s. allocation_trace s (SND (compile_extcall_store_values ce vs buf off s))
Proof
  gen_tac >> Induct >> simp[compile_extcall_store_values_def] >>
  gen_tac >> PairCases_on `h` >> simp[compile_extcall_store_values_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_stage_intcall_args_allocation_trace[simp]:
  !ce vs flags tys s. allocation_trace s (SND (compile_stage_intcall_args ce vs flags tys s))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt strip_tac >>
  simp[Once compile_stage_intcall_args_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_default_return_path_allocation_trace[simp]:
  !ce rt dt buf result def addr skip minsz maxsz info s.
    allocation_trace s (SND (compile_default_return_path ce rt dt buf result def addr skip minsz maxsz info s))
Proof
  rpt gen_tac >> simp[compile_default_return_path_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_external_call_kwargs_allocation_trace[simp]:
  !ce addr vals tys memsz abisz mid retsz minsz retmem static value gas skip hasdef def rt dt enc dec s.
    allocation_trace s (SND (compile_external_call_kwargs ce addr vals tys memsz abisz mid retsz minsz retmem static value gas skip hasdef def rt dt enc dec s))
Proof
  rpt gen_tac >> simp[compile_external_call_kwargs_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_ext_call_kwarg_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt k e s. allocation_trace s (SND (compile_ext_call_kwarg cfn ce rt k e s))
Proof
  rpt strip_tac >> simp[compile_ext_call_kwarg_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[]) >>
  irule lower_value_child_allocation_trace >> simp[]
QED

Theorem compile_ext_call_kwargs_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt ks es s. allocation_trace s (SND (compile_ext_call_kwargs cfn ce rt ks es s))
Proof
  rpt gen_tac >> strip_tac >>
  gen_tac >> Induct_on `ks` >> Cases_on `es` >> rpt strip_tac >>
  simp[Once compile_ext_call_kwargs_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, pairarg_tac] >> simp[]) >>
  irule compile_ext_call_kwarg_allocation_trace >> simp[]
QED
