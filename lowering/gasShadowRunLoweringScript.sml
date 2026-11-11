Theory gasShadowRunLowering
Ancestors
  gasShadowUnitGuards gasShadowUnitExtract gasShadowUnit gasShadowRuntime
  gasShadowState gasShadowModuleDefs vyperCompiler moduleLowering compileEnv
  list pair

Theorem gas_shadow_run_lowering:
  !sels exts ints fb rp buckets metadata dense info entry.
  OPTREL gas_shadow_unit
    (run_lowering sels exts ints fb rp buckets metadata dense info entry)
    (run_lowering sels (MAP gas_shadow_external_package exts)
      (MAP gas_shadow_internal_package ints)
      (OPTION_MAP gas_shadow_fallback_package fb) rp buckets metadata dense info entry)
Proof
  rpt gen_tac >> Cases_on `lowering_policy_ok rp` >- (
    `gas_shadow_state
       (SND (compile_generate_runtime sels exts ints fb rp.rpol_frontend_dispatch
         buckets metadata dense info (initial_compile_state entry)))
       (SND (compile_generate_runtime sels (MAP gas_shadow_external_package exts)
         (MAP gas_shadow_internal_package ints) (OPTION_MAP gas_shadow_fallback_package fb)
         rp.rpol_frontend_dispatch buckets metadata dense info (initial_compile_state entry)))`
      by metis_tac[gas_shadow_compile_generate_runtime, gas_shadow_compiles_def,
                   gas_shadow_state_refl] >>
    qmatch_asmsub_abbrev_tac `gas_shadow_state s t` >>
    `OPTREL (\(c,data) (d,data'). gas_shadow_context c d /\ data = data')
       (extract_context_with_internals entry ints s)
       (extract_context_with_internals entry (MAP gas_shadow_internal_package ints) t)`
      by metis_tac[gas_shadow_extract_context_with_internals] >>
    simp[run_lowering_def] >> pairarg_tac >> gvs[] >> pairarg_tac >>
    gvs[] >> rename1 `gas_shadow_state s t` >>
    Cases_on `extract_context_with_internals entry ints s` >>
    Cases_on `extract_context_with_internals entry (MAP gas_shadow_internal_package ints) t` >>
    gvs[] >> PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
    `lowering_context_ok x0 <=> lowering_context_ok x'0`
      by metis_tac[gas_shadow_lowering_context_ok] >>
    simp[] >> IF_CASES_TAC >> simp[gas_shadow_unit_def]) >>
  simp[run_lowering_def]
QED
