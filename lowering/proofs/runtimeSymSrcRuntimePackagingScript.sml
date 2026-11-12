Theory runtimeSymSrcRuntimePackaging
Ancestors
  runtimeSymSrcInterfaces compileVyper finite_map

Theorem runtime_sym_allocate_args:
  !sft args off vars vars' off'.
    (!n loc. FLOOKUP vars n = SOME loc ==> runtime_sym_loc loc) /\
    allocate_args sft args off vars = (vars',off') ==>
    !n loc. FLOOKUP vars' n = SOME loc ==> runtime_sym_loc loc
Proof
  gen_tac >> Induct >> simp[allocate_args_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[allocate_args_def] >>
  strip_tac >>
  qpat_x_assum `!off vars vars' off'. _`
    (qspecl_then [`off + type_mem_bytes sft h1`,
                  `vars |+ (h0, MemLoc off (type_mem_bytes sft h1))`] mp_tac) >>
  simp[] >> impl_tac >- (rw[FLOOKUP_UPDATE] >> gvs[runtime_sym_loc_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem runtime_sym_module_locations:
  !tops vars.
    (!n loc. FLOOKUP vars n = SOME loc ==> runtime_sym_loc loc) ==>
    !n loc. FLOOKUP (add_module_var_locations tops vars) n = SOME loc ==>
      runtime_sym_loc loc
Proof
  rpt strip_tac >> drule add_module_var_locations_FLOOKUP >>
  strip_tac >> gvs[runtime_sym_loc_def] >> metis_tac[]
QED

Theorem runtime_sym_immutable_locations:
  !sft tops off vars.
    (!n loc. FLOOKUP vars n = SOME loc ==> runtime_sym_loc loc) ==>
    !n loc. FLOOKUP (add_immutable_locations sft tops off vars) n = SOME loc ==>
      runtime_sym_loc loc
Proof
  rpt strip_tac >> drule add_immutable_locations_FLOOKUP >>
  strip_tac >> gvs[runtime_sym_loc_def] >> metis_tac[]
QED

Theorem runtime_sym_build_compile_env:
  runtime_sym_env (build_compile_env tops vis mut name args ret (stmts:stmt list) trans)
Proof
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[runtime_sym_env_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `allocate_args _ _ _ _ = _`) runtime_sym_allocate_args >> simp[] >>
      disch_then drule >> simp[])
  >- (match_mp_tac runtime_sym_immutable_locations >>
      match_mp_tac runtime_sym_module_locations >> simp[])
  >> gvs[allocate_internal_special_vars_def, AllCaseEqs(), runtime_sym_loc_def]
QED
