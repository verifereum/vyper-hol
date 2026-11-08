Theory bodyPtrBytestringBuiltinsCallAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsPairAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsCallStagingAllocationTrace
          bodyPtrBytestringBuiltinsCreatePrimitiveAllocationTrace
          bodyPtrBytestringBuiltinsCreateAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace exprLowering

Theorem compile_call_internal_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt ty id args def s.
    allocation_trace s (SND (compile_call cfn ce rt ty (IntCall id) args def s))
Proof
  rpt strip_tac >> simp[compile_call_def] >>
  pairarg_tac >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[]) >>
  TRY (irule compile_multi_vvs_allocation_trace >> simp[]) >>
  Cases_on `return_buf` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[])
QED


Theorem compile_call_external_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt ty static skip info opts args def s.
    allocation_trace s (SND (compile_call cfn ce rt ty (ExtCall static skip info opts) args def s))
Proof
  rpt strip_tac >> PairCases_on `info` >> Cases_on `args` >>
  simp[compile_call_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd, lower_value_child_allocation_trace,
            compile_multi_vvs_allocation_trace, compile_ext_call_kwargs_allocation_trace]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >>
  Cases_on `v2` >> simp[] >>
  TRY (PairCases_on `x` >> simp[]) >>
  Cases_on `v1` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[])
QED

Theorem compile_call_send_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt ty gas args def s.
    allocation_trace s (SND (compile_call cfn ce rt ty (Send gas) args def s))
Proof
  rpt strip_tac >> Cases_on `args` >>
  TRY (rename1 `h::t` >> Cases_on `t`) >>
  simp[compile_call_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd, lower_value_child_allocation_trace]) >>
  Cases_on `t'` >> simp[] >>
  TRY (rename1 `h'::t` >> Cases_on `t` >> simp[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair] >>
       simp[lower_value_child_allocation_trace]) >>
  irule lower_value_child_allocation_trace >> simp[]
QED

Theorem compile_call_raw_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt ty flags args def s.
    allocation_trace s (SND (compile_call cfn ce rt ty (RawCallTarget flags) args def s))
Proof
  rpt strip_tac >> Cases_on `args` >>
  TRY (rename1 `h::t` >> Cases_on `t`) >>
  simp[compile_call_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd, lower_value_child_allocation_trace,
            compile_ext_call_kwargs_allocation_trace]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >> Cases_on `v1` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[])
QED

Theorem compile_call_raw_calldata_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !rt ty flags args def s.
    allocation_trace s (SND (compile_call cfn ce rt ty (RawCallCalldataTarget flags) args def s))
Proof
  rpt strip_tac >> Cases_on `args` >> simp[compile_call_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd, lower_value_child_allocation_trace,
            compile_ext_call_kwargs_allocation_trace]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >> Cases_on `v1` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >> simp[])
QED

Theorem compile_call_allocation_trace:
  !cfn. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !ce rt ty target args def s.
    allocation_trace s (SND (compile_call cfn ce rt ty target args def s))
Proof
  rpt strip_tac >> Cases_on `target` >>
  simp[compile_call_internal_allocation_trace, compile_call_external_allocation_trace,
       compile_call_send_allocation_trace, compile_call_raw_allocation_trace,
       compile_call_raw_calldata_allocation_trace, compile_call_def, as_stack_val_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair] >>
       simp[allocation_trace_emit_inst_snd, compile_create_call_allocation_trace]) >>
  Cases_on `compile_create_call cfn ce c b b0 args s` >> simp[as_stack_val_def] >>
  metis_tac[compile_create_call_allocation_trace, pairTheory.SND]
QED
