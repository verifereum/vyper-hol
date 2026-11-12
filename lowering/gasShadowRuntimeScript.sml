(* Runtime generator correspondence on arbitrary related compiler states. *)
Theory gasShadowRuntime
Ancestors
  gasShadowModuleDefs gasShadowCompileStmt gasShadowCompileStmtBase
  gasShadowState gasShadow moduleLowering list compileEnv
  gasShadowRuntimeOps gasShadowRuntimeDispatch gasShadowRuntimeBodies gasShadowInternal

Theorem gas_shadow_compile_generate_runtime:
  !sels exts ints fb dispatch buckets metadata dense entry_info.
    gas_shadow_compiles
      (compile_generate_runtime sels exts ints fb dispatch buckets
        metadata dense entry_info)
      (compile_generate_runtime sels
        (MAP gas_shadow_external_package exts)
        (MAP gas_shadow_internal_package ints)
        (OPTION_MAP gas_shadow_fallback_package fb)
        dispatch buckets metadata dense entry_info)
Proof
  rpt gen_tac >> rewrite_tac[compile_generate_runtime_def, LET_THM] >>
  BETA_TAC >> rewrite_tac[comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_fresh_label] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `dispatch` >>
      simp[gas_shadow_compiles_compile_selector_dispatch_linear,
           gas_shadow_compiles_compile_selector_dispatch_sparse,
           gas_shadow_compiles_compile_selector_dispatch_dense]) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_compile_external_fn_bodies] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_new_block] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `fb` >> simp[gas_shadow_compiles_emit_inst] >>
      PairCases_on `x` >>
      simp[gas_shadow_fallback_package_def,
           gas_shadow_compiles_compile_fallback_body]) >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compile_internal_fn_bodies]
QED

Theorem gas_shadow_compile_generate_grouped_runtime:
  !groups ints fb.
  gas_shadow_compiles
    (compile_generate_grouped_runtime groups ints fb)
    (compile_generate_grouped_runtime
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
      (OPTION_MAP gas_shadow_fallback_package fb))
Proof
  rpt gen_tac >>
  rewrite_tac[compile_generate_grouped_runtime_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_fresh_label] >>
  gen_tac >> BETA_TAC >>
  irule gas_shadow_compiles_bind_mapped >>
  qexists_tac `MAP (\job. case job of
    ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
  | ExternalCommonJob common kwvars => ExternalCommonJob
      (common with ec_body := MAP gas_shadow_stmt common.ec_body)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars))` >>
  reverse conj_tac >- simp[gas_shadow_compile_group_dispatch_linear] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_compile_external_jobs] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_new_block] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `fb` >> simp[gas_shadow_compiles_emit_inst] >>
      PairCases_on `x` >>
      simp[gas_shadow_fallback_package_def,
           gas_shadow_compiles_compile_fallback_body]) >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compile_internal_fn_bodies]
QED
