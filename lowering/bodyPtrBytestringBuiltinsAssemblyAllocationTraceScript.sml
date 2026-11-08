Theory bodyPtrBytestringBuiltinsAssemblyAllocationTrace
Ancestors bodyPtrBytestringBuiltinsStoreAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace exprLowering context compileEnv emitHelper

Theorem compile_materialize_vv_allocation_trace[simp]:
  !cenv ty vv s. allocation_trace s (SND (compile_materialize_vv cenv ty vv s))
Proof
  rpt gen_tac >> simp[compile_materialize_vv_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_ifexp_arm_allocation_trace[simp]:
  !cenv rt at vv s. allocation_trace s (SND (compile_ifexp_arm cenv rt at vv s))
Proof
  rpt gen_tac >> simp[compile_ifexp_arm_def] >> IF_CASES_TAC >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem lower_value_allocation_trace:
  !cfn cenv.
  (!ty e s. allocation_trace s (SND (cfn cenv ty e s))) ==>
  !ty e s. allocation_trace s (SND (lower_value cfn cenv ty e s))
Proof
  rpt strip_tac >> simp[lower_value_def] >>
  irule allocation_trace_bind >> simp[]
QED

Theorem compile_struct_lit_allocation_trace:
  !cfn cenv.
  (!ty e s. allocation_trace s (SND (cfn cenv ty e s))) ==>
  !ty fields buf off s.
    allocation_trace s (SND (compile_struct_lit cfn cenv ty fields buf off s))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> Induct >>
  simp[compile_struct_lit_def] >> rpt gen_tac >> PairCases_on `h` >>
  simp[compile_struct_lit_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_expr_body_ifexp_allocation_trace:
  !cfn bfn tfn cenv.
  (!ty e s. allocation_trace s (SND (cfn cenv ty e s))) ==>
  !ty ann cond yes no s.
    allocation_trace s
      (SND (compile_expr_body cfn bfn tfn cenv ty (IfExp ann cond yes no) s))
Proof
  rpt strip_tac >> simp[compile_expr_body_def] >>
  drule lower_value_allocation_trace >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac allocation_trace_fresh_var >>
  imp_res_tac allocation_trace_fresh_label >>
  imp_res_tac allocation_trace_new_block >>
  imp_res_tac allocation_trace_emit_inst >>
  `allocation_trace s st1` by metis_tac[pairTheory.SND] >>
  `allocation_trace st7 st7a` by metis_tac[pairTheory.SND] >>
  `allocation_trace st11 st11a` by metis_tac[pairTheory.SND] >>
  `allocation_trace st7a st8` by metis_tac[compile_ifexp_arm_allocation_trace, pairTheory.SND] >>
  `allocation_trace st11a st12` by metis_tac[compile_ifexp_arm_allocation_trace, pairTheory.SND] >>
  IF_CASES_TAC >> simp[] >>
  map_every (fn mid => irule allocation_trace_trans >> qexists_tac mid >>
    reverse conj_tac >- simp[])
    [`st14`, `st13`, `st12`, `st11a`, `st11`, `st10`, `st9`, `st8`,
     `st7a`, `st7`, `st6`, `st5`, `st4`, `st3`, `st2`, `st1`] >> simp[]
QED
