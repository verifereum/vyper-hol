(* Source origins of the storage and transient roots of retained snapshots. *)
Theory createCtorStorageBaseOriginMods
Ancestors
  compileUnit compileVyper compileEnv bodyInvSplit bodyInvCodeProps
  exprLowering exprSimPopNestedBase targetPlaceSim bodyAugPlaceTarget
  vyperPlaceMutationSoundness vyperInterpreter vyperState vyperAST vyperValue
  finite_map alist list option context

Theorem storage_annotated_src_lookup[local]:
  !tops src vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_src src tops vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_src_def] >>
  Cases >> simp[add_annotated_immutables_src_def] >>
  rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule_all >>
  simp[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem storage_annotated_mods_lookup[local]:
  !mods vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_mods mods vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_mods_def] >>
  PairCases >> simp[add_annotated_immutables_mods_def] >>
  rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >>
  drule_all_then ACCEPT_TAC storage_annotated_src_lookup
QED

Theorem storage_location_src_lookup[local]:
  !tops owner vars src id loc.
    FLOOKUP (add_module_var_locations_src owner tops vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    (src = owner /\ find_var_decl_by_name id tops <> NONE)
Proof
  Induct >> simp[add_module_var_locations_src_def] >>
  Cases >> simp[add_module_var_locations_src_def, find_var_decl_by_name_def] >>
  rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem storage_location_mods_lookup[local]:
  !mods vars src id loc.
    ALL_DISTINCT (MAP FST mods) /\
    FLOOKUP (add_module_var_locations_mods mods vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    ?tops. ALOOKUP mods src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  Induct >> simp[add_module_var_locations_mods_def] >>
  PairCases >> simp[add_module_var_locations_mods_def] >>
  rename1 `MEM owner (MAP FST rest)` >>
  rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac)
  >- (drule_then strip_assume_tac storage_location_src_lookup >> simp[]) >>
  Cases_on `owner = src` >> gvs[] >>
  `ALOOKUP rest owner = NONE` by simp[ALOOKUP_NONE] >> gvs[]
QED

Theorem storage_unit_lookup[local]:
  FLOOKUP (add_immutable_locations_unit sft mods vars) key = SOME loc /\
  (!off. loc <> ImmutableLoc off) ==>
  FLOOKUP vars key = SOME loc
Proof
  Cases_on `mods`
  >- simp[add_immutable_locations_unit_def, add_annotated_immutables_mods_def] >>
  rename1 `FLOOKUP (add_immutable_locations_unit _ (entry::rest) _) _ = _` >>
  Cases_on `rest` >> PairCases_on `entry` >>
  rename1 `FLOOKUP (add_immutable_locations_unit _ ((owner,_)::_) _) _ = _` >>
  Cases_on `owner` >> simp[add_immutable_locations_unit_def] >>
  rpt strip_tac >>
  metis_tac[add_immutable_locations_FLOOKUP, storage_annotated_mods_lookup]
QED

Theorem storage_location_tables[local]:
  contract_inv mods exps ctx cenv cx ==>
  ALL_DISTINCT (MAP FST mods) /\
  cenv.ce_module_vars = add_immutable_locations_unit
    (get_struct_fields (make_struct_fields_map_mods mods)) mods
    (add_module_var_locations_mods mods FEMPTY)
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def]
QED

Theorem module_storage_decl_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME loc /\
  ((?slot. loc = StorageLoc slot) \/ (?slot. loc = TransientLoc slot)) ==>
  ?tops. ALOOKUP mods src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  strip_tac >>
  `!off. loc <> ImmutableLoc off` by fs[] >>
  drule_then strip_assume_tac storage_location_tables >>
  qpat_assum `cenv.ce_module_vars = _` (fn eq =>
    qpat_assum `FLOOKUP cenv.ce_module_vars _ = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all_then assume_tac storage_unit_lookup >>
  drule_all_then strip_assume_tac storage_location_mods_lookup >> gvs[]
QED

Theorem storage_target_root_mods[local]:
  !bt f cenv sa op loc pt sb mods exps ctx cx.
    contract_inv mods exps ctx cenv cx /\
    compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    ~immutable_root cx bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- simp[immutable_root_def, target_root_def]
  >- (PairCases_on `p` >> rpt gen_tac >>
      simp[compile_get_target_ptr_def, LET_THM] >>
      rpt BasicProvers.TOP_CASE_TAC >> simp[comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `?tops. ALOOKUP mods p0 = SOME tops /\ find_var_decl_by_name p1 tops <> NONE` by
        (irule module_storage_decl_mods >> metis_tac[]) >>
      `get_module_code cx p0 = SOME tops` by
        (drule_then (qspec_then `p0` assume_tac) contract_inv_module_codes >> simp[]) >>
      gvs[immutable_root_def, target_root_def]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  rpt BasicProvers.TOP_CASE_TAC >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  PairCases_on `result` >> gvs[] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  metis_tac[immutable_root_def, target_root_def]
QED

Theorem storage_target_not_immutable_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_target_place cx bt es = (INL p,es1) ==>
  !src id path. p <> ImmutablePlace src id path
Proof
  strip_tac >>
  `~immutable_root cx bt` by (irule storage_target_root_mods >> metis_tac[]) >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[aug_place_base_immutable_origin]
QED

Theorem pop_nonvalue[local]:
  (!src id path. p <> ImmutablePlace src id path) /\
  pop_place cx p es = (INL pv,es1) ==> !v. pv <> Value v
Proof
  Cases_on `p` >> simp[] >> strip_tac
  >~ [`pop_place _ (MemoryPlace _ _) _ = _`]
  >- (drule pop_memory_place_success >> strip_tac >> gvs[]) >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  Cases_on `t` >> simp[pop_place_def, raise_def] >>
  rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
  simp[pop_place_def, raise_def, bind_def, ignore_bind_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ctor_storage_base_origin_mods:
  contract_inv mods exps ctx cenv cx /\
  (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  Cases_on `e` >> simp[]
  >- (PairCases_on `p'` >> strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars (p'0,p'1)` >>
      gvs[] >> rpt BasicProvers.TOP_CASE_TAC >>
      rpt (pairarg_tac >> gvs[]) >> disch_tac >> gvs[mk_ptr_def] >>
      `?tops. ALOOKUP mods p'0 = SOME tops /\ find_var_decl_by_name p'1 tops <> NONE` by
        (irule module_storage_decl_mods >> metis_tac[]) >>
      `get_module_code cx p'0 = SOME tops` by
        (drule_then (qspec_then `p'0` assume_tac) contract_inv_module_codes >> simp[]) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, lookup_global_def] >>
      Cases_on `find_var_decl_by_name p'1 tops` >> gvs[] >>
      PairCases_on `x` >> Cases_on `x0` >>
      simp[bind_def, ignore_bind_def, lift_option_type_def,
           return_def, raise_def, record_storage_event_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      rewrite_tac[nested_pop_compile_eq] >> simp[LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `loc_opt` >> simp[mk_ptr_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `!src id path. p <> ImmutablePlace src id path` by
        (irule storage_target_not_immutable_mods >> metis_tac[]) >>
      simp[expr_type_def] >> irule pop_nonvalue >> metis_tac[])
QED
