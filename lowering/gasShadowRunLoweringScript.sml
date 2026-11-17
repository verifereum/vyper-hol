Theory gasShadowRunLowering
Ancestors
  gasShadowUnitGuards gasShadowUnitExtract gasShadowUnit gasShadowRuntime
  gasShadowState gasShadowModuleDefs vyperCompiler moduleLowering compileVyper compileEnv
  list pair


(* The compiler shadow is fixed by the source and policy, before any
   execution state is supplied. This is the ordinary runtime lowering
   spine with its packaged bodies replaced by their GAS shadows. *)
Definition runtime_gas_shadow_unit_def:
  runtime_gas_shadow_unit tops rpolicy =
    let (exts,ints,fb,ctor) = classify_functions tops in
    let selectors = build_selectors (type_env tops) exts in
    let packs = MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts in
    let ips = MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) F 0) ints in
    let fall = set_fallback_package_target rpolicy.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot) fb) in
    run_lowering selectors (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0
      ([] : dense_bucket list) (build_dense_entry_info selectors packs) "__entry"
End

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


Theorem runtime_gas_shadow_unit_exists:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops = (exts,ints,fb,ctor) /\
  ~EXISTS external_has_defaults exts ==>
  ?shadow_unit.
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    gas_shadow_unit unit shadow_unit
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `run_lowering sels packs ips fall rpolicy 0 0 [] info "__entry"` >>
  `OPTREL gas_shadow_unit (SOME unit)
    (run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0 [] info "__entry")` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = SOME unit`
       (SUBST1_TAC o SYM) >> irule gas_shadow_run_lowering) >>
  Cases_on `run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0 [] info "__entry"` >>
  gvs[optionTheory.OPTREL_def] >>
  rename1 `gas_shadow_unit unit shadow_unit` >>
  qexists_tac `shadow_unit` >>
  gvs[runtime_gas_shadow_unit_def, Abbr `sels`, Abbr `packs`, Abbr `ips`,
      Abbr `fall`, Abbr `info`]
QED

Theorem gas_shadow_run_grouped_lowering:
  !groups ints fb rp entry.
  OPTREL gas_shadow_unit
    (run_grouped_lowering groups ints fb rp entry)
    (run_grouped_lowering
      (MAP (\group. case group of
        ExternalSingle selector package =>
          ExternalSingle selector (gas_shadow_external_package package)
      | ExternalDefaults common entries specs head_offset =>
          ExternalDefaults
            (common with ec_body := MAP gas_shadow_stmt common.ec_body)
            entries
            (MAP (\(name,ty,e). (name,ty,gas_shadow_expr e)) specs)
            head_offset) groups)
      (MAP gas_shadow_internal_package ints)
      (OPTION_MAP gas_shadow_fallback_package fb) rp entry)
Proof
  rpt gen_tac >>
  qspecl_then [`groups`, `ints`, `fb`] mp_tac
    gas_shadow_compile_generate_grouped_runtime >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`initial_compile_state entry`,
                           `initial_compile_state entry`] mp_tac) >>
  simp[gas_shadow_state_refl] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_shadow_state s t` >>
  `OPTREL (\(c,data) (d,data'). gas_shadow_context c d /\ data = data')
     (extract_context_with_internals entry ints s)
     (extract_context_with_internals entry (MAP gas_shadow_internal_package ints) t)`
    by metis_tac[gas_shadow_extract_context_with_internals] >>
  Cases_on `lowering_policy_ok rp` >> simp[run_grouped_lowering_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `gas_shadow_state s t` >>
  Cases_on `extract_context_with_internals entry ints s` >>
  Cases_on `extract_context_with_internals entry (MAP gas_shadow_internal_package ints) t` >>
  gvs[] >> PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
  `lowering_context_ok x0 <=> lowering_context_ok x'0`
    by metis_tac[gas_shadow_lowering_context_ok] >>
  simp[] >> IF_CASES_TAC >> simp[gas_shadow_unit_def]
QED
