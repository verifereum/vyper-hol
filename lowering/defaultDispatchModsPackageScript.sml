Theory defaultDispatchModsPackage
Ancestors
  compileUnit compileVyper compileEnv finite_map

(* Both linked package builders use the same environment for this declaration. *)
Theorem empty_fallback_external_package_unit:
  set_fallback_package_target target
    (package_fallback_fn_unit mods use_trans nkeys
      (SOME (src,(mut,nr,rr,name,[],([]:expr list),ret,fbody)))) =
    SOME (ce,pay,nr',key,ut,iv,body',rt) ==>
  set_external_package_target target
    (package_external_fn_unit mods use_trans nkeys
      (src,(mut,nr,rr,name,[],([]:expr list),ret,fbody))) =
    ("fn_" ++ name,ce,[],4,pay,nr',key,ut,iv,body',rt) /\ ce.ce_vars = FEMPTY
Proof
  simp[package_fallback_fn_unit_def, package_external_fn_unit_def,
       set_fallback_package_target_def, set_external_package_target_def,
       build_positional_args_def, min_calldata_size_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `build_flag_info_mods mods (K (K 0)) (K 0)` >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_unit_def, allocate_args_def]
QED
