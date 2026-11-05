Theory bodyPtrPopGlobalNoFrame
Ancestors
  bodyPtrPopGlobalDecomposition bodyPtrPopCallContainment
  bodyPtrPopContextContainment fragExec list

Theorem pop_global_no_containment:
  !ret_ty sa vv sb name fn.
    compile_expr pop_global_package_env ret_ty
      (Pop (BaseT (UintT 256)) pop_global_target) sa = (vv,sb) /\
    venomInst$lookup_function name pop_global_runtime_context.ctx_functions = SOME fn ==>
    ~fn_has_code sa sb fn
Proof
  rpt strip_tac >>
  drule pop_global_call_decomposition >> strip_tac >>
  `fn_has_code sc sd fn` by metis_tac[fn_has_code_mid] >>
  drule_all pop_compile_intcall_fn_invoke >> strip_tac >>
  drule pop_global_lookup_no_invoke >>
  simp[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED
