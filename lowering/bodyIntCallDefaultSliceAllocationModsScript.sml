(* Allocation at the selected default slice, without changing the run pin. *)
Theory bodyIntCallDefaultSliceAllocationMods
Ancestors
  bodyFullIntCallArgs intCallAllocationProps vyperTypeContractStaticMaps
  vyperTypeContract bodyInvSplit compileUnit compileEnv constSubstMods
  allocLimits loweringShapeProps alist list vyperContext vyperTypeSystem

Theorem selected_deploy_defaults_nil[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret ss) tops ==>
  dflts = []
Proof
  strip_tac >> drule_all check_contract_toplevel_decl_MEM_checked >>
  Cases_on `dflts` >> simp[check_toplevel_decl_def, function_header_ok_def]
QED

Theorem selected_source_internal[local]:
  !mods src tops mut nr rr name args dflts ret ss.
    ALOOKUP mods src = SOME tops /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
    MEM (src,(mut,nr,rr,name,args,dflts,ret,ss)) (unit_internal_fns mods)
Proof
  Induct >> simp[] >> qx_gen_tac `m` >> PairCases_on `m` >>
  simp[unit_internal_fns_def] >> pairarg_tac >> gvs[] >>
  simp[MEM_MAP] >>
  qspec_then `m1` mp_tac classify_fold_internal >> simp[] >>
  disch_tac >> rpt gen_tac >> Cases_on `m0 = src` >> gvs[] >> metis_tac[]
QED

Theorem selected_classified_internal[local]:
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  MEM (src,subst_consts_fn_mods (consts_env_mods mods)
      (mut,nr,rr,name,args,dflts,ret,ss))
    (FST (SND (classify_functions_unit mods exps)))
Proof
  strip_tac >> drule_all selected_source_internal >> strip_tac >>
  simp[classify_functions_unit_def] >> pairarg_tac >> gvs[MEM_MAP] >>
  qexists_tac `(src,mut,nr,rr,name,args,dflts,ret,ss)` >> simp[]
QED

Theorem selected_alloc_drop[local]:
  !ds n. alloc_limits_exprs ce ds ==> alloc_limits_exprs ce (DROP n ds)
Proof
  Induct >> simp[alloc_limits_expr_def] >>
  gen_tac >> qx_gen_tac `n` >> Cases_on `n` >> fs[alloc_limits_expr_def]
QED

Theorem selected_internal_defaults_alloc[local]:
  contract_inv mods exps ctx cd cx /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  well_typed_exprs (defaults_env ed)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) ==>
  alloc_limits_exprs cd
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))
Proof
  strip_tac >> drule_all selected_classified_internal >>
  disch_then $ qspec_then `exps`
    (assume_tac o REWRITE_RULE [subst_consts_fn_mods_def]) >>
  drule_all contract_inv_internal_allocs >> simp[fn_allocs_ok_unit_def] >>
  strip_tac >> drule_then (qspec_then `n` assume_tac) selected_alloc_drop >>
  qmatch_asmsub_abbrev_tac `alloc_limits_exprs fn_env (DROP _ _)` >>
  qmatch_goalsub_abbrev_tac `alloc_limits_exprs cd ds` >>
  `alloc_limits_exprs cd ds = alloc_limits_exprs fn_env ds` suffices_by simp[] >>
  irule intcall_args_pure_allocs_frame >>
  qpat_x_assum `contract_inv _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >>
  simp[Abbr `fn_env`, build_compile_env_unit_def] >>
  rpt (pairarg_tac >> simp[]) >>
  qexists_tac `ed` >> simp[]
QED

Theorem intcall_default_slice_alloc_mods:
  contract_inv mods exps ctx (ce with ce_module := src) cx /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  (vis = Internal \/ vis = Deploy) /\
  well_typed_exprs (defaults_env ed)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) ==>
  alloc_limits_exprs (ce with ce_module := src)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))
Proof
  strip_tac >> gvs[]
  >- (drule_all selected_internal_defaults_alloc >> simp[]) >>
  drule_all selected_deploy_defaults_nil >>
  simp[constSubstModsTheory.subst_consts_expr_mods_def, alloc_limits_expr_def]
QED
