(* Current-state storage read soundness.  Every witness below is decoded from
   the state named in the theorem conclusion; no pre-transition value is used. *)

Theory vyperStorageReadSoundness
Ancestors
  vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend vyperState
  vyperTypeValues
Libs
  wordsLib

(* Persistent and transient ordinary declarations share this boundary. *)
Theorem current_storage_read_typed:
  contract_storage_well_formed cx st /\
  storage_var_info cx mid n = SOME (b,off,tv) ==>
  ?v. read_storage_slot cx b (n2w off) tv st = (INL v,st) /\
      value_has_type tv v
Proof
  rpt strip_tac >>
  `declared_storage_region cx mid n [] = SOME (b,n2w off,tv)` by
    metis_tac[declared_storage_region_ordinary] >>
  `?storage. get_storage_backend cx b st = (INL storage,st)` by
    metis_tac[get_storage_backend_INL] >>
  `slots_in_range storage (w2n ((n2w off):bytes32)) tv` by
    metis_tac[contract_storage_well_formed_region] >>
  `well_formed_type_value tv` by
    (qpat_x_assum `storage_var_info cx mid n = SOME (b,off,tv)` mp_tac >>
     simp[storage_var_info_def, AllCaseEqs()] >>
     metis_tac[evaluate_type_well_formed_type_value]) >>
  `?v. decode_value storage (w2n ((n2w off):bytes32)) tv = SOME v /\
       value_has_type tv v` by
    metis_tac[decode_value_from_slots_in_range] >>
  qexists_tac `v` >>
  gvs[read_storage_slot_def, bind_def, lift_option_def, return_def,
      wordsTheory.w2n_n2w]
QED


Theorem storage_var_info_components[local]:
  storage_var_info cx mid n = SOME (b,off,tv) ==>
  ?code typ id.
    get_module_code cx mid = SOME code /\
    find_var_decl_by_num (string_to_num n) code =
      SOME (StorageVarDecl b typ,id) /\
    lookup_var_slot_from_layout cx b mid id = SOME off /\
    evaluate_type (get_tenv cx) typ = SOME tv
Proof
  simp[storage_var_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (goal_assum $ drule_at Any)
QED

(* Scalar and non-array aggregate declarations are returned directly as Values. *)
Theorem current_storage_lookup_typed:
  contract_storage_well_formed cx st /\
  storage_var_info cx mid n = SOME (b,off,tv) /\
  (!elem bd. tv <> ArrayTV elem bd) ==>
  ?v. lookup_global cx mid (string_to_num n) st = (INL (Value v),st) /\
      value_has_type tv v
Proof
  rpt strip_tac >>
  `?v. read_storage_slot cx b (n2w off) tv st = (INL v,st) /\
       value_has_type tv v` by
    metis_tac[current_storage_read_typed] >>
  drule storage_var_info_components >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  Cases_on `tv` >> gvs[] >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       var_decl_info_CASE_rator]
QED

(* Top-level arrays remain references at lookup; materialisation performs the
   current storage read proved above. *)
Theorem current_storage_array_materialise_typed:
  contract_storage_well_formed cx st /\
  storage_var_info cx mid n = SOME (b,off,ArrayTV elem_tv bd) ==>
  ?v. lookup_global cx mid (string_to_num n) st =
        (INL (ArrayRef b (n2w off) elem_tv bd),st) /\
      materialise cx (ArrayRef b (n2w off) elem_tv bd) st = (INL v,st) /\
      value_has_type (ArrayTV elem_tv bd) v
Proof
  rpt strip_tac >>
  `?v. read_storage_slot cx b (n2w off) (ArrayTV elem_tv bd) st =
         (INL v,st) /\ value_has_type (ArrayTV elem_tv bd) v` by
    metis_tac[current_storage_read_typed] >>
  drule storage_var_info_components >> strip_tac >>
  qexists_tac `v` >>
  simp[lookup_global_def, materialise_def, bind_def, lift_option_type_def,
       return_def, raise_def, var_decl_info_CASE_rator]
QED

Theorem current_storage_non_array_materialise_typed:
  contract_storage_well_formed cx st /\
  storage_var_info cx mid n = SOME (b,off,tv) /\
  (!elem bd. tv <> ArrayTV elem bd) ==>
  ?ref v. lookup_global cx mid (string_to_num n) st = (INL ref,st) /\
          materialise cx ref st = (INL v,st) /\
          value_has_type tv v
Proof
  rpt strip_tac >>
  drule_all current_storage_lookup_typed >> strip_tac >>
  qexistsl [`Value v`,`v`] >>
  simp[materialise_def, return_def]
QED

(* Uniform whole-value materialisation, while preserving the interpreter's
   distinction between ArrayRef lookup and direct Value lookup. *)
Theorem current_storage_materialise_typed:
  contract_storage_well_formed cx st /\
  storage_var_info cx mid n = SOME (b,off,tv) ==>
  ?ref v. lookup_global cx mid (string_to_num n) st = (INL ref,st) /\
          materialise cx ref st = (INL v,st) /\
          value_has_type tv v
Proof
  rpt strip_tac >> Cases_on `tv`
  >- (irule current_storage_non_array_materialise_typed >> simp[])
  >- (irule current_storage_non_array_materialise_typed >> simp[])
  >- (drule_all current_storage_array_materialise_typed >> strip_tac >>
      metis_tac[])
  >- (irule current_storage_non_array_materialise_typed >> simp[])
  >- (irule current_storage_non_array_materialise_typed >> simp[])
  >- (irule current_storage_non_array_materialise_typed >> simp[])
QED
val _ = export_theory();
