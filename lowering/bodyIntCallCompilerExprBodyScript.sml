Theory bodyIntCallCompilerExprBody
Ancestors
  bodyIntCallCompilerCall bodyIntCallCompilerLiteral
  bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerCallRoots
  bodyIntCallCompilerAggregate bodyIntCallCompilerContext bodyIntCallCompilerFloor
  bodyIntCallCompilerEmit bodyIntCallCompilerInterval exprLowering exprOperandVar

Theorem intcall_interval_expr_ifexp[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_expr_body cfn bfn tfn ce ty (IfExp ann cond te ee) a))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_fresh_var,
            intcall_interval_fresh_label, intcall_interval_emit_inst,
            intcall_interval_new_block, intcall_interval_ifexp_arm] >>
       rpt strip_tac) >>
  IF_CASES_TAC >> simp[intcall_compiler_interval_refl]
QED

Theorem intcall_interval_expr_struct[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_expr_body cfn bfn tfn ce ty (StructLit ann nm fs) a))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_struct_lit_all,
            intcall_compiler_interval_refl] >> rpt strip_tac) >>
  simp[intcall_compiler_interval_refl]
QED

Theorem intcall_interval_expr_pop[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_expr_body cfn bfn tfn ce ty (Pop ann target) a))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_get_target_ptr_all, intcall_interval_dynarray_pop,
            pairTheory.FORALL_PROD, intcall_compiler_interval_refl] >>
       rpt strip_tac) >>
  simp[intcall_compiler_interval_refl]
QED

Theorem intcall_interval_expr_builtin[local]:
  (!ce rt ty bi es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (bfn ce rt ty bi es a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_expr_body cfn bfn tfn ce ty (Builtin ann bi es) a))
Proof
  strip_tac >>
  irule (BETA_RULE (Q.SPEC `\p. intcall_compiler_interval k a (SND p)`
           compiler_expr_builtin_pred)) >>
  simp[intcall_interval_addmod_names, intcall_interval_mulmod_names,
       intcall_interval_powmod256_names]
QED

Theorem intcall_interval_expr_body:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  (!ce rt ty bi es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (bfn ce rt ty bi es a))) /\
  (!ce vt ty tb rt es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (tfn ce vt ty tb rt es a))) ==>
  !ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_expr_body cfn bfn tfn ce ty e a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `e` >>
  simp[intcall_interval_expr_ifexp, intcall_interval_expr_struct,
       intcall_interval_expr_pop, intcall_interval_expr_builtin] >>
  simp[compile_expr_body_def, intcall_interval_literal_vv,
       intcall_interval_name_vv, intcall_interval_attribute_all,
       intcall_interval_subscript_all, intcall_interval_call,
       intcall_compiler_interval_refl] >>
  strip_tac >> rename1 `FLOOKUP ce.ce_module_vars nsid` >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[intcall_compiler_interval_refl]
  >- (ho_match_mp_tac intcall_interval_pair_bind_floor >>
      simp[intcall_interval_emit_inst, intcall_compiler_interval_refl]) >>
  rename1 `SOME vl` >> Cases_on `vl` >>
  simp[intcall_compiler_interval_refl] >>
  ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[intcall_interval_emit_inst, intcall_compiler_interval_refl]
QED
