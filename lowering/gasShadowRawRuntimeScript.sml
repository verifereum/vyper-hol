(* Both raw lowering results agree on failure and retain complete metadata. *)
Theory gasShadowRawRuntime
Ancestors
  gasShadowUnit gasShadowRuntime gasShadowModuleDefs gasShadow
  gasShadowRunLowering gasShadowSourcePackages gasShadowSourceMetadata
  gasShadowAllocLimits compileVyper vyperCompiler list option pair

(* Shadowing keeps the defaults lists' lengths, so it never changes whether
   the grouped (keyword-default) runtime path is taken. *)
Theorem exists_external_has_defaults_shadow[local]:
  !l. EXISTS external_has_defaults
        (MAP (\(m,n,r,f,a,d,t,b).
               (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) l) <=>
      EXISTS external_has_defaults l
Proof
  Induct >> simp[] >> rpt strip_tac >> PairCases_on `h` >>
  simp[external_has_defaults_def, NULL_EQ]
QED

(* The grouped runtime path (external functions with keyword defaults) has no
   gas-shadow correspondence yet; the supported subset has no defaults. *)
Theorem gas_shadow_lower_vyper_runtime_unit:
  !tops rp.
    ~EXISTS external_has_defaults (FST (classify_functions tops)) ==>
    OPTREL gas_shadow_unit
      (lower_vyper_runtime_unit tops rp)
      (lower_vyper_runtime_unit (MAP gas_shadow_toplevel tops) rp)
Proof
  rpt gen_tac >> strip_tac >>
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
  `EXISTS external_has_defaults classified0 <=> F`
    by fs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >>
  IF_CASES_TAC >>
  simp[exists_external_has_defaults_shadow, gas_shadow_run_lowering]
QED

