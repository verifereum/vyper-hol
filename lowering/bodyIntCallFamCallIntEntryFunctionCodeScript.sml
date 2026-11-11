(* Constructor-safe ownership of the actual internal-function entry interval. *)
Theory bodyIntCallFamCallIntEntryFunctionCode
Ancestors
  intCallCallee externalEntryShape fragExec compileEnv
Libs
  monadsyntax

Theorem intcall_function_entry_labels:
  !ce params rb ctor il rt s.
    cs_extends s (SND (compile_internal_function_entry ce params rb ctor il rt s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_internal_function_entry ce params rb ctor il rt s)))
Proof
  rpt gen_tac >>
  rewrite_tac[compile_internal_function_entry_def,
              compile_internal_entry_prefix_def] >>
  rpt (FIRST [CHANGED_TAC (simp[comp_return_labels, emit_op_labels,
    compile_internal_param_decls_labels, materialize_internal_params_labels,
    compile_fixed_region_with_id_labels, compile_alloc_buffer_labels]),
    irule comp_bind_labels >> conj_tac,
    irule comp_ignore_bind_labels >> conj_tac,
    gen_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC])
QED

Theorem intcall_function_entry_code:
  !ce params rb nr key tr view ctor il body rt b c callee.
    compile_internal_function ce params rb nr key tr view ctor il body rt b = ((),c) /\
    fn_has_code b c callee ==>
    ?ce2 rpc immopt m.
      compile_internal_function_entry ce params rb ctor il rt b =
        ((ce2,rpc,immopt),m) /\
      cs_extends b m /\ cs_extends m c /\ fn_has_code b m callee
Proof
  rpt gen_tac >>
  rewrite_tac[compile_internal_function_entry_factorization] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `comp_bind _ suffix b` >>
  `!entry s. cs_extends s (SND (suffix entry s)) /\
     EVERY (isPREFIX "@") (added_labels s (SND (suffix entry s)))` by
    (simp[Abbr `suffix`] >> rpt gen_tac >>
     rpt (FIRST [CHANGED_TAC (simp[comp_return_labels,
       compile_nonreentrant_lock_labels, stmt_context_helpers_labels,
       compile_stmt_labels, comp_get_labels, emit_inst_labels]),
       irule comp_bind_labels >> conj_tac,
       irule comp_ignore_bind_labels >> conj_tac,
       gen_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC])) >>
  Cases_on `compile_internal_function_entry ce params rb ctor il rt b` >>
  rename1 `compile_internal_function_entry ce params rb ctor il rt b = (entry,m)` >>
  PairCases_on `entry` >>
  gvs[comp_bind_def] >>
  `cs_extends b
     (SND (compile_internal_function_entry ce params rb ctor il rt b))` by
    simp[intcall_function_entry_labels] >>
  gvs[] >>
  `cs_extends m c` by
    (first_x_assum (qspecl_then [`(entry0,entry1,entry2)`,`m`] mp_tac) >> simp[]) >>
  metis_tac[fn_has_code_split]
QED
