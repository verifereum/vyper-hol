(* Both raw lowering results agree on failure and retain complete metadata. *)
Theory gasShadowRawRuntime
Ancestors
  gasShadowUnit gasShadowRuntime gasShadowModuleDefs gasShadow
  gasShadowRunLowering gasShadowSourcePackages gasShadowSourceMetadata
  gasShadowAllocLimits compileVyper vyperCompiler list option pair

Theorem gas_shadow_lower_vyper_runtime_unit:
  !tops rp.
    OPTREL gas_shadow_unit
      (lower_vyper_runtime_unit tops rp)
      (lower_vyper_runtime_unit (MAP gas_shadow_toplevel tops) rp)
Proof
  rpt gen_tac >>
  qabbrev_tac `classified = classify_functions tops` >>
  PairCases_on `classified` >>
  fs[markerTheory.Abbrev_def] >>
  pop_assum (assume_tac o SYM) >>
  asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [lower_vyper_runtime_unit_def, gas_shadow_classify_functions,
    gas_shadow_type_env, LET_THM,
    pairTheory.pair_case_thm, BETA_THM] >>
  asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [gas_shadow_build_selectors, gas_shadow_map_package_external_fn,
    gas_shadow_map_package_internal_fn, gas_shadow_package_fallback_fn,
    gas_shadow_set_fallback_package_target, gas_shadow_build_dense_entry_info,
    EVERY_APPEND, gas_shadow_every_fn_allocs_ok,
    gas_shadow_fallback_fn_allocs_ok, gas_shadow_every_external_return_buffer_ok] >>
  IF_CASES_TAC >> simp[gas_shadow_run_lowering]
QED

