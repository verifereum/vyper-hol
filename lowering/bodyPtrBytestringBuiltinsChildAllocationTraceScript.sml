Theory bodyPtrBytestringBuiltinsChildAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAssemblyAllocationTrace
          bodyPtrBytestringBuiltinsTupleAllocationTrace
          bodyPtrBytestringBuiltinsStoreAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace exprLowering context compileEnv emitHelper list

Theorem lower_value_child_allocation_trace:
  !cfn cenv ty e.
  (!s. allocation_trace s (SND (cfn cenv ty e s))) ==>
  !s. allocation_trace s (SND (lower_value cfn cenv ty e s))
Proof
  rpt strip_tac >> simp[lower_value_def] >> irule allocation_trace_bind >> simp[]
QED

Theorem compile_make_tuple_child_allocation_trace:
  !cfn cenv es.
  (!e. MEM e es ==> !s. allocation_trace s (SND (cfn cenv (expr_type e) e s))) ==>
  !buf off s. allocation_trace s (SND (compile_make_tuple cfn cenv es buf off s))
Proof
  rpt gen_tac >> Induct_on `es` >> simp[compile_make_tuple_def] >> rpt strip_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_make_array_elems_child_allocation_trace:
  !cfn cenv es.
  (!e. MEM e es ==> !s. allocation_trace s (SND (cfn cenv (expr_type e) e s))) ==>
  !et sz len buf idx s.
    allocation_trace s (SND (compile_make_array_elems cfn cenv es et sz len buf idx s))
Proof
  rpt gen_tac >> Induct_on `es` >> simp[compile_make_array_elems_def] >> rpt strip_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_make_array_child_allocation_trace:
  !cfn cenv es.
  (!e. MEM e es ==> !s. allocation_trace s (SND (cfn cenv (expr_type e) e s))) ==>
  !et sz len buf s.
    allocation_trace s (SND (compile_make_array cfn cenv es et sz len buf s))
Proof
  rpt strip_tac >> simp[compile_make_array_def] >>
  irule allocation_trace_ignore_bind >> conj_tac
  >- (Cases_on `len` >> simp[]) >>
  irule compile_make_array_elems_child_allocation_trace >> simp[]
QED

Theorem compile_multi_exprs_child_allocation_trace:
  !cfn cenv es.
  (!e. MEM e es ==> !s. allocation_trace s (SND (cfn cenv (expr_type e) e s))) ==>
  !s. allocation_trace s (SND (compile_multi_exprs cfn cenv es s))
Proof
  rpt gen_tac >> Induct_on `es` >> simp[compile_multi_exprs_def] >> rpt strip_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[]) >>
  irule lower_value_child_allocation_trace >> simp[]
QED

Theorem compile_struct_lit_child_allocation_trace:
  !cfn cenv fields.
  (!fname e. MEM (fname,e) fields ==>
    !s. allocation_trace s (SND (cfn cenv (expr_type e) e s))) ==>
  !ty buf off s.
    allocation_trace s (SND (compile_struct_lit cfn cenv ty fields buf off s))
Proof
  rpt gen_tac >> Induct_on `fields` >> simp[compile_struct_lit_def] >>
  gen_tac >> PairCases_on `h` >> simp[compile_struct_lit_def] >> rpt strip_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[]) >> metis_tac[]
QED

Theorem compile_attribute_child_allocation_trace:
  !cfn cenv ty base.
  (!s. allocation_trace s (SND (cfn cenv ty base s))) ==>
  !rt field s. allocation_trace s (SND (compile_attribute cfn cenv rt ty base field s))
Proof
  rpt strip_tac >> simp[compile_attribute_def] >>
  irule allocation_trace_bind >> simp[] >>
  rpt gen_tac >> irule allocation_trace_bind >> simp[]
QED

Theorem compile_expr_body_ifexp_child_allocation_trace:
  !cfn bfn tfn cenv ty ann cond yes no.
  (!s. allocation_trace s (SND (cfn cenv (BaseT BoolT) cond s))) /\
  (!s. allocation_trace s (SND (cfn cenv ty yes s))) /\
  (!s. allocation_trace s (SND (cfn cenv ty no s))) ==>
  !s. allocation_trace s
      (SND (compile_expr_body cfn bfn tfn cenv ty (IfExp ann cond yes no) s))
Proof
  rpt strip_tac >> simp[compile_expr_body_def] >>
  `!s. allocation_trace s (SND (lower_value cfn cenv (BaseT BoolT) cond s))` by
    (irule lower_value_child_allocation_trace >> simp[]) >>
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
