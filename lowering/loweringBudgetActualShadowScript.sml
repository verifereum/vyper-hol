(* Static correspondence for the supplied deterministic shadow compilation.
   This does not assert source GAS observation-order correspondence. *)
Theory loweringBudgetActualShadow
Ancestors
  loweringShapeProps gasShadowRunLowering gasShadowModuleDefs gasShadowUnit
  compileVyper vyperCompiler

Theorem lower_budget_actual_shadow_context:
  !tops rpolicy unit exts ints fb ctor sels packs ips fall shadow_unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    classify_functions tops = (exts,ints,fb,ctor) /\
    sels = build_selectors (type_env tops) exts /\
    packs =
      MAP (set_external_package_target rpolicy.rpol_target o
           package_external_fn tops T (K global_nonreentrant_slot)) exts /\
    ips =
      MAP (set_internal_package_target rpolicy.rpol_target o
           package_internal_fn tops T (K global_nonreentrant_slot) F 0) ints /\
    fall =
      set_fallback_package_target rpolicy.rpol_target
        (package_fallback_fn tops T (K global_nonreentrant_slot) fb) /\
    run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0 []
      (build_dense_entry_info sels packs) "__entry" = SOME shadow_unit /\
    supported_program tops ==>
    gas_shadow_context unit.cu_context shadow_unit.cu_context
Proof
  rpt strip_tac >>
  `~EXISTS external_has_defaults exts` by
    (drule supported_program_no_external_defaults >> simp[]) >>
  `run_lowering sels packs ips fall rpolicy 0 0 []
     (build_dense_entry_info sels packs) "__entry" = SOME unit` by
    (qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
     simp[lower_vyper_runtime_unit_def] >>
     IF_CASES_TAC >> simp[]) >>
  `OPTREL gas_shadow_unit
     (run_lowering sels packs ips fall rpolicy 0 0 []
       (build_dense_entry_info sels packs) "__entry")
     (run_lowering sels (MAP gas_shadow_external_package packs)
       (MAP gas_shadow_internal_package ips)
       (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0 []
       (build_dense_entry_info sels packs) "__entry")` by
    irule gas_shadow_run_lowering >>
  gvs[gas_shadow_unit_def]
QED
