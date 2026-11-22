Theory defaultDispatchModsRun
Ancestors
  compileUnit compileVyper compileEnv loweringShapeDefs bodyFullShadowInternalCode list

(* The default-free linked runtime uses the ordinary dispatcher. *)
Theorem default_unit_linear_run:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  ~EXISTS (external_has_defaults o SND) exts ==>
  ?ips.
    run_lowering (build_selectors (type_env_all_modules mods) (MAP SND exts)) (MAP
      (set_external_package_target rp.rpol_target o package_external_fn_unit mods T (K
      global_nonreentrant_slot)) exts) ips (set_fallback_package_target rp.rpol_target
      (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb)) rp 0 0 []
      (build_dense_entry_info (build_selectors (type_env_all_modules mods) (MAP SND exts)) (MAP
        (set_external_package_target rp.rpol_target o package_external_fn_unit mods T (K
        global_nonreentrant_slot)) exts)) "__entry" = SOME unit /\
    EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl)
      (MAP (set_external_package_target rp.rpol_target o package_external_fn_unit mods T (K
        global_nonreentrant_slot)) exts) /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0)
    (order_internals_unit
      (runtime_internal_order_unit (exported_runtime_fns mods exps)
        (main_module mods) ints) ints)` >>
  qexists_tac `ips` >> rpt conj_tac
  >- (qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
      simp[lower_vyper_runtime_unit_mods_def, AllCaseEqs(), Abbr `ips`])
  >- (simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `src` >> PairCases_on `src` >>
      simp[package_external_fn_unit_def, set_external_package_target_def,
           jump_label_ok_def]) >>
  simp_tac std_ss [Abbr `ips`, internal_fn_descriptors_map, EVERY_MAP,
                   combinTheory.o_DEF] >>
  simp[EVERY_MEM] >> qx_gen_tac `src` >> PairCases_on `src` >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def,
       internal_label_ok_def, internal_fn_label_def]
QED
