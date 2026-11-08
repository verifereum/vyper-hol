(* The runtime data payload is the same in both related deploy units. *)
Theory gasShadowRawDeploy
Ancestors
  gasShadowUnit gasShadowDeploy gasShadowModuleDefs gasShadow
  compileVyper vyperCompiler list option pair
  gasShadowSourceMetadata gasShadowSourcePackages gasShadowAllocLimits gasShadowDeployRunner

Theorem gas_shadow_lower_vyper_deploy_unit:
  !tops rp runtime_bytes.
    OPTREL gas_shadow_unit
      (lower_vyper_deploy_unit tops rp runtime_bytes)
      (lower_vyper_deploy_unit (MAP gas_shadow_toplevel tops) rp runtime_bytes)
Proof
  rpt gen_tac >>
  simp[lower_vyper_deploy_unit_def, gas_shadow_classify_functions] >>
  pairarg_tac >> gvs[] >>
  `!f : function_mutability # bool # bool # identifier # argument list # expr list # type # stmt list. fn_allocs_ok (MAP gas_shadow_toplevel tops)
     ((\(mut,nr,rr,name,args,defaults,ret,body).
       (mut,nr,rr,name,args,MAP gas_shadow_expr defaults,ret,MAP gas_shadow_stmt body)) f) =
     fn_allocs_ok tops f` by
    (gen_tac >> PairCases_on `f` >> simp[gas_shadow_fn_allocs_ok]) >>
  `!fs : (function_mutability # bool # bool # identifier # argument list # expr list # type # stmt list) list. EXISTS ($~ o fn_allocs_ok (MAP gas_shadow_toplevel tops))
       (MAP (\(mut,nr,rr,name,args,defaults,ret,body).
          (mut,nr,rr,name,args,MAP gas_shadow_expr defaults,ret,MAP gas_shadow_stmt body)) fs) =
       EXISTS ($~ o fn_allocs_ok tops) fs` by
    (simp[EXISTS_MAP, EXISTS_MEM, combinTheory.o_DEF] >> metis_tac[]) >>
  qpat_x_assum `!fs. EXISTS _ _ = _` (qspec_then `int_fns` assume_tac) >>
  simp[gas_shadow_compute_immutables_len] >>
  Cases_on `ctor_fn`
  >- (simp[set_constructor_package_target_def, ctor_named_init_def] >>
      IF_CASES_TAC >> simp[] >>
      irule (SRULE [] (Q.INST [`ints` |-> `[]`, `stmts` |-> `[]`]
        (SPEC_ALL gas_shadow_run_deploy_lowering)))) >>
  PairCases_on `x` >>
  simp[gas_shadow_fn_allocs_ok, gas_shadow_package_constructor,
       gas_shadow_set_constructor_package_target, ctor_named_init_def] >>
  IF_CASES_TAC >> simp[] >>
  `MAP (set_internal_package_target rp.rpol_target o
        package_internal_fn (MAP gas_shadow_toplevel tops) T (K global_nonreentrant_slot) T
         (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops))
       (MAP (\(mut,nr,rr,name,args,defaults,ret,body).
          (mut,nr,rr,name,args,MAP gas_shadow_expr defaults,ret,MAP gas_shadow_stmt body)) int_fns) =
   MAP gas_shadow_internal_package
       (MAP (set_internal_package_target rp.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) T
         (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops)) int_fns)` by
    (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[] >>
     gen_tac >> strip_tac >> PairCases_on `x` >>
     simp[gas_shadow_package_internal_fn, gas_shadow_set_internal_package_target]) >>
  simp[] >> pairarg_tac >> gvs[] >>
  simp[gas_shadow_set_constructor_package_target] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `set_constructor_package_target _ (_ (package_constructor _ _ _ _)) = _` mp_tac >>
  pairarg_tac >> gvs[set_constructor_package_target_def] >>
  strip_tac >> gvs[] >> irule gas_shadow_run_deploy_lowering
QED
