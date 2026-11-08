Theory bodyPtrBytestringBuiltinsScalarAllocationTrace
Ancestors bodyPtrBytestringBuiltinsLiteralAllocationTrace
          bodyPtrBytestringBuiltinsHashAllocationTrace
          bodyPtrBytestringBuiltinsSimpleAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace
          bodyPtrBytestringBuiltinsSubscriptAllocationTrace exprLowering exprBopLowering

Theorem compile_invert_allocation_trace[simp]:
  !v ty ce s. allocation_trace s (SND (compile_invert v ty ce s))
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_invert_def]
QED

Theorem compile_neg_allocation_trace[simp]:
  !v ty s. allocation_trace s (SND (compile_neg v ty s))
Proof
  rpt gen_tac >> simp[compile_neg_def] >> pairarg_tac >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_env_var_allocation_trace[simp]:
  !item s. allocation_trace s (SND (compile_env_var item s))
Proof
  Cases >> simp[compile_env_var_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_acc_allocation_trace:
  !cfn ce e item.
  (!ty s. allocation_trace s (SND (cfn ce ty e s))) ==>
  !s. allocation_trace s (SND (compile_acc cfn ce e item s))
Proof
  rpt strip_tac >>
  `!ty s. allocation_trace s (SND (lower_value cfn ce ty e s))` by
    (rpt gen_tac >> irule lower_value_child_allocation_trace >> simp[]) >>
  Cases_on `item` >> simp[compile_acc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (qpat_x_assum `emit_inst INVALID _ _ _ = _`
        (mp_then Any mp_tac allocation_trace_emit_inst) >> simp[] >> NO_TAC) >>
  qpat_x_assum `!ty s. allocation_trace s (SND (lower_value _ _ _ _ s))`
    (qspecl_then [`BaseT AddressT`, `s`] mp_tac) >> simp[] >> strip_tac >>
  irule allocation_trace_trans >> qexists `st1` >> conj_tac >- simp[] >>
  simp[] >>
  rename1 `emit_op EXTCODESIZE _ st1 = (_,st2)` >>
  irule allocation_trace_trans >> qexists `st2` >> reverse conj_tac >- simp[] >>
  drule allocation_trace_emit_op >> simp[]
QED

Theorem compile_dynarray_pop_allocation_trace[simp]:
  !base ws sz ctor imm loc s.
    allocation_trace s (SND (compile_dynarray_pop base ws sz ctor imm loc s))
Proof
  rpt gen_tac >> simp[compile_dynarray_pop_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_addmod_names_allocation_trace[simp]:
  !ce rt at a bt b mt m s.
    allocation_trace s (SND (compile_addmod_names ce rt at a bt b mt m s))
Proof
  rpt gen_tac >> simp[compile_addmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `allocation_trace s st1` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st1 st2` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  `allocation_trace st2 st3` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st3 st4` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  `allocation_trace st4 st5` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st5 st6` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  irule allocation_trace_trans >> qexists `st6` >> reverse conj_tac >- simp[as_stack_val_pair] >>
  metis_tac[allocation_trace_trans]
QED

Theorem compile_mulmod_names_allocation_trace[simp]:
  !ce rt at a bt b mt m s.
    allocation_trace s (SND (compile_mulmod_names ce rt at a bt b mt m s))
Proof
  rpt gen_tac >> simp[compile_mulmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `allocation_trace s st1` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st1 st2` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  `allocation_trace st2 st3` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st3 st4` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  `allocation_trace st4 st5` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st5 st6` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  irule allocation_trace_trans >> qexists `st6` >> reverse conj_tac >- simp[as_stack_val_pair] >>
  metis_tac[allocation_trace_trans]
QED

Theorem compile_powmod256_names_allocation_trace[simp]:
  !ce rt at a bt b s.
    allocation_trace s (SND (compile_powmod256_names ce rt at a bt b s))
Proof
  rpt gen_tac >> simp[compile_powmod256_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `allocation_trace s st1` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st1 st2` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  `allocation_trace st2 st3` by metis_tac[compile_name_vv_allocation_trace, pairTheory.SND] >>
  `allocation_trace st3 st4` by metis_tac[unwrap_value_allocation_trace, pairTheory.SND] >>
  irule allocation_trace_trans >> qexists `st4` >> reverse conj_tac >- simp[as_stack_val_pair] >>
  metis_tac[allocation_trace_trans]
QED

Theorem compile_get_target_ptr_allocation_trace:
  !cfn ce.
  (!ce' ty e s. allocation_trace s (SND (cfn ce' ty e s))) ==>
  !bt s. allocation_trace s (SND (compile_get_target_ptr cfn ce bt s))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >> rpt gen_tac >>
  simp[Once compile_get_target_ptr_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind,
              irule lower_value_child_allocation_trace,
              irule compile_array_subscript_allocation_trace,
              IF_CASES_TAC, BasicProvers.TOP_CASE_TAC,
              first_x_assum irule] >> simp[])
QED
