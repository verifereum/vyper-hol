(* Runtime generator correspondence on arbitrary related compiler states. *)
Theory gasShadowRuntime
Ancestors
  gasShadowModuleDefs gasShadowCompileStmt gasShadowCompileStmtBase
  gasShadowState gasShadow moduleLowering list compileEnv
  gasShadowRuntimeDispatch gasShadowRuntimeBodies gasShadowInternal

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
