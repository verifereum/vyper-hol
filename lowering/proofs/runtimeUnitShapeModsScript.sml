Theory runtimeUnitShapeMods
Ancestors
  list pair rich_list string compileUnit compileVyper compileEnv
  compileUnitPackageShape loweringShapeProps loweringShapeSource
  loweringUnitEntryShape intCallLookup vyperCompiler vyperTypeContract
  unitShapeDefs o1PassContract venomInst loweringShapeDefs

Theorem package_external_fn_unit_shape_dynamic[local]:
  external_fn_shape_mode_ok F
    (set_external_package_target target (package_external_fn_unit mods trans nkeys sf))
Proof
  PairCases_on `sf` >>
  qabbrev_tac `ce = build_compile_env_unit mods sf0 External sf1 sf4 sf5 sf7 sf8 trans` >>
  `cenv_static_mode_ok F ce /\ (External <> Internal ==> ce.ce_return_pc = NONE)` by
    (unabbrev_all_tac >> match_mp_tac build_compile_env_unit_static_mode >>
     simp[expr_shape_root_mode_dynamic, EVERY_MEM, dynamic_raw_expr_shape]) >>
  Cases_on `sf7 = NoneT` >>
  gvs[package_external_fn_unit_def, set_external_package_target_def,
      external_fn_shape_mode_ok_def, update_cenv_ret_abi_def,
      update_cenv_nonreentrant_def, cenv_static_mode_ok_def,
      expr_shape_root_mode_dynamic, dynamic_raw_stmt_shape] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem package_external_group_unit_shape_from_package[local]:
  external_fn_shape_mode_ok F
    (set_external_package_target target (package_external_fn_unit mods trans nkeys sf)) ==>
  external_group_shape_mode_ok F (package_external_group_unit mods target trans nkeys sf)
Proof
  strip_tac >> PairCases_on `sf` >>
  simp[package_external_group_unit_def] >> IF_CASES_TAC >> simp[]
  >- simp[external_group_shape_mode_ok_def, compute_selector_def, IS_PREFIX_APPEND] >>
  qmatch_asmsub_abbrev_tac `external_fn_shape_mode_ok F pkg` >>
  PairCases_on `pkg` >>
  fs[external_fn_shape_mode_ok_def, external_group_shape_mode_ok_def,
     external_common_shape_mode_ok_def, external_common_label_def,
     jump_label_ok_def, IS_PREFIX_APPEND] >>
  conj_tac
  >- simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, external_prefix_label_def,
          compute_selector_def, IS_PREFIX_APPEND] >>
  simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
       expr_shape_root_mode_dynamic, dynamic_raw_expr_shape]
QED

Theorem lower_vyper_runtime_unit_source_unit_ok_mods:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
  check_contract F layouts addr mods = SOME art ==>
  o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  strip_tac >>
  Cases_on `classify_functions_unit mods exps` >>
  PairCases_on `r` >>
  rename1 `classify_functions_unit _ _ = (exts,ints,fb,_,_)` >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  qpat_x_assum `classify_functions_unit _ _ = _` (fn th =>
    pure_rewrite_tac[lower_vyper_runtime_unit_mods_def, th, LET_THM]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  (* The outer guard only selects the successful branch. *)
  qmatch_goalsub_abbrev_tac `(if admitted then (if _ then _ else _) else NONE) = SOME _` >>
  qpat_x_assum `Abbrev (admitted = _)` kall_tac >>
  reverse (Cases_on `admitted` >> pure_rewrite_tac[COND_CLAUSES])
  >- simp[] >>
  qmatch_goalsub_abbrev_tac `run_grouped_lowering _ ips fps _ _` >>
  `EVERY (internal_fn_shape_mode_ok F) ips /\
   EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    (qpat_assum `Abbrev (ips = _)`
       (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     dxrule (Q.INST [`static` |-> `F`] package_internal_fn_unit_shape) >>
     (impl_tac >-
       simp[EVERY_MEM, FORALL_PROD, expr_shape_root_mode_dynamic,
            dynamic_raw_expr_shape, dynamic_raw_stmt_shape]) >>
     disch_then ACCEPT_TAC) >>
  `fallback_shape_mode_ok F fps` by
    (simp[Abbr `fps`] >> Cases_on `fb`
     >- simp[package_fallback_fn_unit_def, set_fallback_package_target_def,
             fallback_shape_mode_ok_def] >>
     qmatch_goalsub_rename_tac `SOME sf` >>
     `external_fn_shape_mode_ok F
        (set_external_package_target rpolicy.rpol_target
          (package_external_fn_unit mods T (K global_nonreentrant_slot) sf))` by
       simp[package_external_fn_unit_shape_dynamic] >>
     PairCases_on `sf` >>
     gvs[package_external_fn_unit_def, set_external_package_target_def,
         external_fn_shape_mode_ok_def, package_fallback_fn_unit_def,
         set_fallback_package_target_def, fallback_shape_mode_ok_def]) >>
  disch_tac >>
  `o1_source_unit_ok unit /\
   EVERY (\i. ~is_param_opcode i.inst_opcode)
     (fn_insts (HD unit.cu_context.ctx_functions)) /\
   lowering_context_ok unit.cu_context` by
    (qpat_x_assum `(if _ then _ else _) = SOME _` mp_tac >>
     Cases_on `EXISTS (external_has_defaults o SND) exts`
     >- (Cases_on `EVERY (external_defaults_no_sha256 o SND) exts` >>
         simp[] >> strip_tac >>
         qpat_x_assum `EXISTS (external_has_defaults o SND) _` kall_tac >>
         qpat_x_assum `EVERY (external_defaults_no_sha256 o SND) _` kall_tac >>
         qmatch_asmsub_abbrev_tac `run_grouped_lowering groups _ _ _ _` >>
         `EVERY (external_group_shape_mode_ok F) groups` by
           (simp[Abbr `groups`, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
            irule package_external_group_unit_shape_from_package >>
            simp[package_external_fn_unit_shape_dynamic]) >>
         `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
           (qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
            simp[run_grouped_lowering_def] >> pairarg_tac >>
            simp[AllCaseEqs()] >> metis_tac[extract_context_descriptors_distinct]) >>
         drule run_grouped_lowering_context >> strip_tac >>
         drule_all (Q.INST [`static` |-> `F`] run_grouped_lowering_source_unit_ok_mode) >>
         simp[]) >>
     simp[] >> strip_tac >>
     qpat_x_assum `~EXISTS (external_has_defaults o SND) _` kall_tac >>
     qmatch_asmsub_abbrev_tac `run_lowering sels eps _ _ _ _ _ _ _ _` >>
     `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
       simp[Abbr `sels`, build_selectors_fn_labels] >>
     `EVERY (external_fn_shape_mode_ok F) eps` by
       simp[Abbr `eps`, EVERY_MAP, EVERY_MEM, package_external_fn_unit_shape_dynamic] >>
     drule run_lowering_descriptors_distinct >> strip_tac >>
     drule run_lowering_context_ok >> strip_tac >>
     drule_all (Q.INST [`static` |-> `F`] run_lowering_source_unit_ok_mode) >>
     simp[]) >>
  simp[] >> irule unit_entry_no_params_from_first >>
  fs[lowering_context_ok_def, ctx_fn_names_def]
QED
