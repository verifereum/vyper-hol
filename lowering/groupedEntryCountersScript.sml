(* Counter bounds for the grouped dispatcher and its entry initializers. *)
Theory groupedEntryCounters
Ancestors
  exprLoweringProps exprLowering moduleLowering
  abiEncoder compileEnv groupedKeywordAllocas list pair

fun counter_steps ths =
  rpt (FIRST [
    CHANGED_TAC (simp (ths @ [ci_mono_comp_return, ci_mono_emit_op,
      ci_mono_emit_void, ci_mono_emit_inst, ci_mono_new_block, ci_mono_fresh_label])),
    ho_match_mp_tac ci_mono_bind >> conj_tac,
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac,
    gen_tac,
    IF_CASES_TAC]);

Theorem compile_init_kwargs_ci_mono:
  !vars ce off k hi st. ci_mono st (SND (compile_init_kwargs ce vars off k hi st))
Proof
  Induct >- simp[compile_init_kwargs_def, ci_mono_comp_return] >>
  qx_gen_tac `item` >> PairCases_on `item` >> rpt gen_tac >>
  simp_tac bool_ss [compile_init_kwargs_def, LET_THM] >>
  counter_steps [compile_abi_arg_ptr_guard_def, CONJUNCT1 ci_mono_compile_abi_decode,
    ci_mono_lower_value_compile_expr, ci_mono_compile_store_bytestring]
QED

Theorem compile_entry_point_kwargs_ci_mono:
  ci_mono st (SND (compile_entry_point_kwargs ce vars off k label st))
Proof
  rewrite_tac[compile_entry_point_kwargs_def] >>
  counter_steps [compile_init_kwargs_ci_mono]
QED

Theorem compile_entry_checks_ci_mono:
  ci_mono st (SND (compile_entry_checks mincd payable st))
Proof
  rewrite_tac[compile_entry_checks_def] >> counter_steps []
QED

Theorem compile_group_entries_ci_mono:
  !entries st. ci_mono st (SND (compile_group_entries mid entries common vars off st))
Proof
  Induct >- simp[compile_group_entries_def, ci_mono_comp_return] >>
  qx_gen_tac `item` >> PairCases_on `item` >> gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_group_entries_def] >>
  counter_steps [compile_entry_checks_ci_mono, compile_entry_point_kwargs_ci_mono]
QED

Theorem compile_selector_checks_ci_mono:
  !sels st. ci_mono st (SND (compile_selector_checks mid sels st))
Proof
  Induct >- simp[compile_selector_checks_def, ci_mono_comp_return] >>
  qx_gen_tac `item` >> PairCases_on `item` >> gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_selector_checks_def] >>
  counter_steps []
QED

Theorem compile_external_groups_ci_mono:
  !groups st. ci_mono st (SND (compile_external_groups mid groups st))
Proof
  Induct >- simp[compile_external_groups_def, ci_mono_comp_return] >>
  Cases
  >- (rename1 `ExternalSingle selector pkg` >> PairCases_on `selector` >>
      gen_tac >> PURE_ONCE_REWRITE_TAC[compile_external_groups_def] >>
      counter_steps [compile_selector_checks_ci_mono]) >>
  gen_tac >> PURE_ONCE_REWRITE_TAC[compile_external_groups_def] >>
  counter_steps [compile_create_kwarg_allocas_mono, compile_group_entries_ci_mono]
QED
