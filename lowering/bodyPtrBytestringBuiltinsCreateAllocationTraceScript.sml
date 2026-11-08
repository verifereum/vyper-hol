Theory bodyPtrBytestringBuiltinsCreateAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsCallStagingAllocationTrace
          bodyPtrBytestringBuiltinsCreatePrimitiveAllocationTrace
          bodyPtrBytestringBuiltinsAbiEncodeAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace exprLowering

Theorem compile_create_salt_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !salt s. allocation_trace s (SND (compile_create_salt cfn ce salt s))
Proof
  rpt gen_tac >> strip_tac >> Cases >> simp[compile_create_salt_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[]) >>
  irule lower_value_child_allocation_trace >> simp[]
QED

Theorem compile_create_ctor_tuple_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !args s. allocation_trace s (SND (compile_create_ctor_tuple cfn ce args s))
Proof
  rpt strip_tac >> simp[compile_create_ctor_tuple_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[]) >>
  irule compile_multi_vvs_allocation_trace >> simp[]
QED

Theorem compile_create_blueprint_args_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !raw args s. allocation_trace s (SND (compile_create_blueprint_args cfn ce raw args s))
Proof
  rpt strip_tac >> Cases_on `args` >> simp[compile_create_blueprint_args_def] >>
  TRY (rename1 `h::t` >> Cases_on `t` >> simp[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd]) >>
  FIRST [irule lower_value_child_allocation_trace,
         irule compile_create_ctor_tuple_allocation_trace] >> simp[]
QED

Theorem compile_create_snapshot_allocation_trace[simp]:
  !ce vv ty s. allocation_trace s (SND (compile_create_snapshot ce vv ty s))
Proof
  rpt gen_tac >> simp[compile_create_snapshot_def] >>
  irule allocation_trace_bind >> simp[] >> rpt gen_tac >>
  irule allocation_trace_ignore_bind >> simp[] >>
  Cases_on `vv_location vv` >> simp[] >>
  TRY (rename1 `SOME loc` >> Cases_on `loc` >> simp[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_raw_create_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !code value args salt rev s.
    allocation_trace s (SND (compile_raw_create cfn ce code value args salt rev s))
Proof
  rpt strip_tac >> simp[compile_raw_create_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  FIRST [irule lower_value_child_allocation_trace,
         irule compile_create_ctor_tuple_allocation_trace,
         irule compile_create_salt_allocation_trace] >> simp[]
QED

Theorem compile_create_call_allocation_trace:
  !cfn ce. (!env ty e s. allocation_trace s (SND (cfn env ty e s))) ==>
  !ck salt rev args s.
    allocation_trace s (SND (compile_create_call cfn ce ck salt rev args s))
Proof
  rpt strip_tac >> Cases_on `args`
  >- (simp[compile_create_call_def] >> irule allocation_trace_ignore_bind >>
      simp[allocation_trace_emit_inst_snd]) >>
  rename1 `compile_create_call cfn ce ck salt rev (target::rest)` >>
  Cases_on `rest`
  >- (simp[compile_create_call_def] >> irule allocation_trace_ignore_bind >>
      simp[allocation_trace_emit_inst_snd]) >>
  Cases_on `ck` >> simp[compile_create_call_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC, pairarg_tac] >>
       simp[allocation_trace_emit_inst_snd]) >>
  FIRST [irule lower_value_child_allocation_trace,
         irule compile_create_salt_allocation_trace,
         irule compile_create_blueprint_args_allocation_trace,
         irule compile_raw_create_allocation_trace] >> simp[]
QED
