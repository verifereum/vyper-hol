(* Origin of non-immutable entries in the linked module location table. *)
Theory linkedStorageLocationOrigin
Ancestors
  bodyInvSplit compileUnit compileVyper compileEnv finite_map vyperState pair alist

Theorem assign_storage_annotated_src_lookup[local]:
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

Theorem assign_storage_annotated_mods_lookup[local]:
  !mods vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_mods mods vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_mods_def] >>
  PairCases >> simp[add_annotated_immutables_mods_def] >>
  rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >>
  drule_all_then ACCEPT_TAC assign_storage_annotated_src_lookup
QED

Theorem assign_storage_location_src_lookup[local]:
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

Theorem assign_storage_location_mods_lookup[local]:
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
  >- (drule_then strip_assume_tac assign_storage_location_src_lookup >> simp[]) >>
  Cases_on `owner = src` >> gvs[] >>
  `ALOOKUP rest owner = NONE` by simp[ALOOKUP_NONE] >> gvs[]
QED

Theorem assign_storage_unit_lookup[local]:
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
  metis_tac[add_immutable_locations_FLOOKUP, assign_storage_annotated_mods_lookup]
QED

Theorem assign_storage_location_tables[local]:
  contract_inv mods exps ctx cenv cx ==>
  ALL_DISTINCT (MAP FST mods) /\
  cenv.ce_module_vars = add_immutable_locations_unit
    (get_struct_fields (make_struct_fields_map_mods mods)) mods
    (add_module_var_locations_mods mods FEMPTY)
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def]
QED

Theorem contract_inv_nonimmutable_module_location:
  contract_inv mods exps ctx ce cx /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME loc /\
  (!off. loc <> ImmutableLoc off) ==>
  ?tops. ALOOKUP mods src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  strip_tac >>
  drule_then strip_assume_tac assign_storage_location_tables >>
  qpat_assum `ce.ce_module_vars = _` (fn eq =>
    qpat_assum `FLOOKUP ce.ce_module_vars _ = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all_then assume_tac assign_storage_unit_lookup >>
  drule_all_then strip_assume_tac assign_storage_location_mods_lookup >> gvs[]
QED
