(* Static provenance only: this boundary does not assert semantic dispatch. *)
Theory loweringBudgetCompilerCuts
Ancestors compileVyper vyperCompiler

Theorem runtime_entry_compiler_provenance:
  !tops rp unit name fn lbl.
    lower_vyper_runtime_unit tops rp = SOME unit /\
    unit.cu_context.ctx_entry = SOME name /\
    lookup_function name unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl ==>
    ?exts ints fb ctor sels exts_pkg ints_pkg fb_pkg groups final ctx data.
      classify_functions tops = (exts,ints,fb,ctor) /\
      sels = build_selectors (type_env tops) exts /\
      exts_pkg = MAP (set_external_package_target rp.rpol_target o
        package_external_fn tops T (K global_nonreentrant_slot)) exts /\
      ints_pkg = MAP (set_internal_package_target rp.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) F 0) ints /\
      fb_pkg = set_fallback_package_target rp.rpol_target
        (package_fallback_fn tops T (K global_nonreentrant_slot) fb) /\
      groups = MAP (package_external_group tops rp.rpol_target T
        (K global_nonreentrant_slot)) exts /\
      lowering_policy_ok rp /\
      (if EXISTS external_has_defaults exts then
         compile_generate_grouped_runtime groups ints_pkg fb_pkg
           (initial_compile_state "__entry") = ((),final)
       else
         compile_generate_runtime sels exts_pkg ints_pkg fb_pkg
           rp.rpol_frontend_dispatch 0 0 ([]:dense_bucket list)
           (build_dense_entry_info sels exts_pkg)
           (initial_compile_state "__entry") = ((),final)) /\
      extract_context_with_internals "__entry" ints_pkg final = SOME (ctx,data) /\
      lowering_context_ok ctx /\
      unit = <| cu_context := ctx; cu_data_segment := data |> /\
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  gvs[lower_vyper_runtime_unit_def, run_grouped_lowering_def,
    run_lowering_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt (goal_assum drule) >> metis_tac[listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF]
QED
