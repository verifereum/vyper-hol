Theory compileUnitPackageShape
Ancestors
  list pair finite_map compileUnit compileVyper compileEnv
  loweringShapeProps loweringShapeSource bodyFullShadowInternalCode
  supportedExprTraverse supportedStmtTraverse
  vyperCompiler venomInst

Theorem expr_shape_root_mode_dynamic:
  expr_shape_root_mode F = expr_raw_shape_root_mode F
Proof
  simp[FUN_EQ_THM, expr_shape_root_mode_def, expr_raw_shape_root_mode_def]
QED

Theorem module_var_locations_src_static[local]:
  !tops src vars.
    (!k loc. FLOOKUP vars k = SOME loc ==> static_loc loc) ==>
    !k loc. FLOOKUP (add_module_var_locations_src src tops vars) k = SOME loc ==>
      static_loc loc
Proof
  Induct >- simp[add_module_var_locations_src_def] >>
  rpt gen_tac >> strip_tac >> simp[add_module_var_locations_src_def] >>
  first_x_assum match_mp_tac >>
  Cases_on `h` >> simp[] >> rpt CASE_TAC >>
  rw[FLOOKUP_UPDATE] >> gvs[static_loc_def] >> metis_tac[]
QED

Theorem module_var_locations_mods_static[local]:
  !mods vars.
    (!k loc. FLOOKUP vars k = SOME loc ==> static_loc loc) ==>
    !k loc. FLOOKUP (add_module_var_locations_mods mods vars) k = SOME loc ==>
      static_loc loc
Proof
  Induct >- simp[add_module_var_locations_mods_def] >>
  Cases_on `h` >> simp[add_module_var_locations_mods_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum match_mp_tac >>
  match_mp_tac module_var_locations_src_static >> first_assum ACCEPT_TAC
QED

Theorem annotated_immutables_src_static[local]:
  !tops src vars.
    (!k loc. FLOOKUP vars k = SOME loc ==> static_loc loc) ==>
    !k loc. FLOOKUP (add_annotated_immutables_src src tops vars) k = SOME loc ==>
      static_loc loc
Proof
  Induct >- simp[add_annotated_immutables_src_def] >>
  Cases_on `h` >> simp[add_annotated_immutables_src_def] >> rpt CASE_TAC >>
  rpt gen_tac >> strip_tac >> first_x_assum match_mp_tac >>
  rw[FLOOKUP_UPDATE] >> gvs[static_loc_def] >> metis_tac[]
QED

Theorem annotated_immutables_mods_static[local]:
  !mods vars.
    (!k loc. FLOOKUP vars k = SOME loc ==> static_loc loc) ==>
    !k loc. FLOOKUP (add_annotated_immutables_mods mods vars) k = SOME loc ==>
      static_loc loc
Proof
  Induct >- simp[add_annotated_immutables_mods_def] >>
  Cases_on `h` >> simp[add_annotated_immutables_mods_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum match_mp_tac >>
  match_mp_tac annotated_immutables_src_static >> first_assum ACCEPT_TAC
QED

Theorem immutable_locations_unit_static[local]:
  (!k loc. FLOOKUP vars k = SOME loc ==> static_loc loc) ==>
  !k loc. FLOOKUP (add_immutable_locations_unit sft mods vars) k = SOME loc ==>
    static_loc loc
Proof
  strip_tac >> Cases_on `mods`
  >- (simp[add_immutable_locations_unit_def, add_annotated_immutables_mods_def] >>
      first_assum ACCEPT_TAC) >>
  PairCases_on `h` >> Cases_on `t`
  >- (Cases_on `h0` >> simp[add_immutable_locations_unit_def]
      >- (rpt strip_tac >> drule add_immutable_locations_FLOOKUP >>
          strip_tac >> gvs[static_loc_def] >> metis_tac[]) >>
      match_mp_tac annotated_immutables_mods_static >> first_assum ACCEPT_TAC) >>
  simp[add_immutable_locations_unit_def] >>
  match_mp_tac annotated_immutables_mods_static >> first_assum ACCEPT_TAC
QED

val _ = Parse.hide "body";

Theorem build_compile_env_unit_static_locations:
  (!k loc. FLOOKUP
     (build_compile_env_unit mods src vis mut fname args ret body use_trans).ce_vars
     k = SOME loc ==> static_loc loc) /\
  (!k loc. FLOOKUP
     (build_compile_env_unit mods src vis mut fname args ret body use_trans).ce_module_vars
     k = SOME loc ==> static_loc loc)
Proof
  simp[build_compile_env_unit_def] >> rpt (pairarg_tac >> gvs[]) >>
  `!k loc. FLOOKUP
     (FST (allocate_args (get_struct_fields (make_struct_fields_map_mods mods))
                        args 0 FEMPTY)) k = SOME loc ==> static_loc loc` by
    (match_mp_tac allocate_args_static >> simp[]) >>
  `!k loc. FLOOKUP
     (add_immutable_locations_unit (get_struct_fields (make_struct_fields_map_mods mods))
       mods (add_module_var_locations_mods mods FEMPTY)) k = SOME loc ==>
     static_loc loc` by
    (match_mp_tac immutable_locations_unit_static >>
     match_mp_tac module_var_locations_mods_static >> simp[]) >>
  qpat_x_assum `allocate_args _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SRULE [] o Q.AP_TERM `FST`) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem build_compile_env_unit_static_mode:
  EVERY (\nd. ~supported_exprs_exists (expr_shape_root_mode static) (SND nd))
    (build_func_defaults_mods mods) ==>
  cenv_static_mode_ok static
    (build_compile_env_unit mods src vis mut fname args ret ss use_trans) /\
  (vis <> Internal ==>
    (build_compile_env_unit mods src vis mut fname args ret ss use_trans).ce_return_pc = NONE)
Proof
  strip_tac >>
  mp_tac (Q.INST [`body` |-> `ss`] build_compile_env_unit_static_locations) >>
  simp[build_compile_env_unit_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  Cases_on `vis = Internal` >>
  gvs[allocate_internal_special_vars_def, AllCaseEqs(), cenv_static_mode_ok_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem package_internal_fn_unit_shape:
  packages =
    MAP (set_internal_package_target target o
         package_internal_fn_unit mods use_trans nkeys is_ctor imm_len) fns /\
  EVERY (\nd. ~supported_exprs_exists (expr_shape_root_mode static) (SND nd))
    (build_func_defaults_mods mods) /\
  EVERY (\(src,mut,nr,rr,name,args,dflts,ret,ss).
    ~supported_stmts_expr_exists (expr_shape_root_mode static) ss) fns ==>
  EVERY (internal_fn_shape_mode_ok static) packages /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors packages)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `EVERY _ fns` mp_tac >>
  Induct_on `fns` >- simp[internal_fn_descriptors_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def,
       internal_fn_descriptors_def] >>
  strip_tac >>
  qpat_x_assum `EVERY _ fns ==> _` drule >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (pure_rewrite_tac[loweringShapeDefsTheory.internal_label_ok_def] >>
      irule internal_fn_label_prefix) >>
  `cenv_static_mode_ok static
     (build_compile_env_unit mods h0 Internal h1 h4 h5 h7 h8 use_trans)` by
    metis_tac[build_compile_env_unit_static_mode] >>
  gvs[internal_fn_shape_mode_ok_def, update_cenv_nonreentrant_def,
      cenv_static_mode_ok_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem extract_context_descriptors_distinct:
  extract_context_with_internals entry packages st = SOME (ctx,data) /\
  lowering_context_ok ctx ==>
  ALL_DISTINCT (MAP FST (internal_fn_descriptors packages))
Proof
  strip_tac >> drule extract_context_internal_names >> strip_tac >>
  fs[lowering_context_ok_def, ctx_fn_names_def]
QED
