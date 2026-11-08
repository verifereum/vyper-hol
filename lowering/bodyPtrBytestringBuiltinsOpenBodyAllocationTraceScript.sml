Theory bodyPtrBytestringBuiltinsOpenBodyAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsStringAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsPairAllocationTrace
          bodyPtrBytestringBuiltinsCallAllocationTrace
          bodyPtrBytestringBuiltinsScalarAllocationTrace
          bodyPtrBytestringBuiltinsConversionAllocationTrace
          bodyPtrBytestringBuiltinsSimpleAllocationTrace
          bodyPtrBytestringBuiltinsHashAllocationTrace
          bodyPtrBytestringBuiltinsAbiAllocationTrace
          bodyPtrBytestringBuiltinsSubscriptAllocationTrace
          bodyPtrBytestringBuiltinsOperatorAllocationTrace exprLowering

Theorem as_ptr_val_snd[simp]:
  !ty loc p. SND (as_ptr_val ty loc p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_ptr_val_def]
QED

Theorem as_stack_val_snd[simp]:
  !ty p. SND (as_stack_val ty p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem compile_type_builtin_dispatch_body_allocation_trace:
  !cfn. (!ce ty e s. allocation_trace s (SND (cfn ce ty e s))) ==>
  !ce vt ty tb rt es s. allocation_trace s
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt es s))
Proof
  rpt strip_tac >> Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, as_stack_val_def, as_ptr_val_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[as_stack_val_def, as_ptr_val_def,
            lower_value_child_allocation_trace, compile_multi_exprs_child_allocation_trace]) >>
  TRY (pairarg_tac >> simp[]) >>
  TRY (rename1 `mk_convert_op _ rt` >> Cases_on `rt` >> simp[]) >>
  rpt gen_tac >> PairCases_on `v` >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair] >>
       simp[lower_value_child_allocation_trace])
QED

Theorem compile_builtin_dispatch_body_allocation_trace:
  !cfn. (!ce ty e s. allocation_trace s (SND (cfn ce ty e s))) ==>
  !ce rt ty bi es s. allocation_trace s
    (SND (compile_builtin_dispatch_body cfn ce rt ty bi es s))
Proof
  rpt strip_tac >> Cases_on `bi` >> simp[compile_builtin_dispatch_body_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[lower_value_child_allocation_trace, compile_acc_allocation_trace,
            compile_concat_allocation_trace, compile_multi_exprs_child_allocation_trace,
            compile_make_tuple_child_allocation_trace, compile_make_array_child_allocation_trace]) >>
  TRY (rename1 `method_id_literal _` >> Cases_on `method_id_literal (HD es)` >> simp[] >>
       rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
                   IF_CASES_TAC] >> simp[lower_value_child_allocation_trace])) >>
  TRY (irule compile_acc_allocation_trace >> simp[]) >>
  TRY (rename1 `compile_var_array_membership _ _ _ (expr_type rhs)` >>
       Cases_on `rhs` >> simp[] >>
       TRY (rename1 `Builtin _ tag _` >> Cases_on `tag` >> simp[]) >>
       rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
                   IF_CASES_TAC] >> simp[compile_multi_exprs_child_allocation_trace])) >>
  TRY (rename1 `compile_make_array cfn ce es` >> Cases_on `o'` >> simp[] >>
       rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair] >>
            simp[compile_make_tuple_child_allocation_trace, compile_make_array_child_allocation_trace])) >>
  TRY (rpt gen_tac >> PairCases_on `v` >> simp[] >>
       rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair] >>
            simp[lower_value_child_allocation_trace])) >>
  Cases_on `expr_type (HD es)` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair] >>
       simp[lower_value_child_allocation_trace])
QED

Theorem allocation_result_map_snd[simp]:
  !f p. SND ((\(x,s). (f x,s)) p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[]
QED

Theorem allocation_list_case_const[local]:
  !xs:'a list. !v:'b. list_CASE xs v (\h t. v) = v
Proof
  Cases >> simp[]
QED

Theorem allocation_expr_case_const[local]:
  !e. !v:'a.
    expr_CASE e (\a b. v) (\a b. v) (\a b c. v) (\a b c d. v)
      (\a b. v) (\a b c. v) (\a b c. v) (\a b c. v) (\a b c. v)
      (\a b c d. v) (\a b. v) (\a b c d. v) = v
Proof
  Cases >> simp[]
QED

Theorem compile_expr_body_allocation_trace:
  !cfn bfn tfn.
  (!ce ty e s. allocation_trace s (SND (cfn ce ty e s))) /\
  (!ce rt ty bi es s. allocation_trace s (SND (bfn ce rt ty bi es s))) /\
  (!ce vt ty tb rt es s. allocation_trace s (SND (tfn ce vt ty tb rt es s))) ==>
  !ce ty e s. allocation_trace s
    (SND (compile_expr_body cfn bfn tfn ce ty e s))
Proof
  rpt strip_tac >> Cases_on `e` >>
  TRY (irule compile_expr_body_ifexp_child_allocation_trace >> simp[]) >>
  simp[compile_expr_body_def,
       compile_subscript_allocation_trace, compile_attribute_child_allocation_trace,
       compile_call_allocation_trace] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, ho_match_mp_tac allocation_trace_pair,
              IF_CASES_TAC] >>
       simp[compile_struct_lit_child_allocation_trace, compile_get_target_ptr_allocation_trace]) >>
  TRY (rpt gen_tac >> PairCases_on `v` >> simp[] >>
       ho_match_mp_tac allocation_trace_pair >> simp[]) >>
  TRY (rename1 `Builtin _ bi _` >> Cases_on `bi` >>
       simp[TypeBase.case_rand_of ``:expr list``, TypeBase.case_rand_of ``:expr``,
            allocation_list_case_const, allocation_expr_case_const]) >>
  TRY (rename1 `FLOOKUP ce.ce_module_vars nsid` >>
       Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[allocation_trace_emit_inst_snd] >>
       Cases_on `x` >> simp[allocation_trace_emit_inst_snd])
QED
