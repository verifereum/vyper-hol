(* Current-state storage read soundness.  Every witness below is decoded from
   the state named in the theorem conclusion; no pre-transition value is used. *)

Theory vyperStorageReadSoundness
Ancestors
  vyperStorageLayoutSafety vyperStorageWritePreservation vyperLookupStorage
  vyperStorageBackend vyperState vyperTypeValues
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

(* Successful semantic region resolution always returns an evaluated, hence
   well-formed, storage type.  This covers ordinary declarations and complete
   nested-hashmap key paths uniformly. *)
Theorem resolve_hashmap_leaf_well_formed_type:
  !tenv root_slot vt subs slot tv.
    resolve_hashmap_leaf tenv root_slot vt subs = SOME (slot,tv) ==>
    well_formed_type_value tv
Proof
  gen_tac >> qx_gen_tac `root_slot` >> qx_gen_tac `vt` >>
  qid_spec_tac `root_slot` >> Induct_on `vt` >> Cases_on `subs` >>
  simp[resolve_hashmap_leaf_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem declared_storage_region_well_formed_type:
  declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
  well_formed_type_value tv
Proof
  simp[declared_storage_region_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[evaluate_type_well_formed_type_value,
            resolve_hashmap_leaf_well_formed_type]
QED

(* Current typed read for any semantically declared ordinary or hashmap region. *)
Theorem current_declared_storage_region_read_typed:
  contract_storage_well_formed cx st /\
  declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
  ?v. read_storage_slot cx b slot tv st = (INL v,st) /\
      value_has_type tv v
Proof
  rpt strip_tac >>
  `get_storage_backend cx b st =
     (INL (get_storage cx st b),st)` by simp[get_storage_backend_eq] >>
  `slots_in_range (get_storage cx st b) (w2n slot) tv` by
    metis_tac[contract_storage_well_formed_region] >>
  `well_formed_type_value tv` by
    metis_tac[declared_storage_region_well_formed_type] >>
  `?v. decode_value (get_storage cx st b) (w2n slot) tv = SOME v /\
       value_has_type tv v` by
    metis_tac[decode_value_from_slots_in_range] >>
  qexists_tac `v` >>
  gvs[read_storage_slot_def, bind_def, lift_option_def, return_def,
      get_storage_backend_eq]
QED

(* Assign-target-facing nested hashmap leaf read.  The split/hash/evaluate
   premises are the interpreter's exact key-path computation, not an opaque
   key certificate. *)
Theorem current_hashmap_leaf_read_typed:
  contract_storage_well_formed cx st /\
  get_module_code cx mid = SOME code /\
  find_var_decl_by_num (string_to_num n) code =
    SOME (HashMapVarDecl b kt vt,id) /\
  lookup_var_slot_from_layout cx b mid id = SOME off /\
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,[]) /\
  compute_hashmap_slot (n2w off) (kt::kts) (first_sub::rest_subs) =
    SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  ?v. read_storage_slot cx b final_slot final_tv st = (INL v,st) /\
      value_has_type final_tv v
Proof
  rpt strip_tac >>
  irule current_declared_storage_region_read_typed >>
  conj_tac
  >- (qexistsl [`mid`, `n`, `first_sub::rest_subs`] >>
      irule declared_hashmap_leaf_agrees_assign_target >> simp[]) >>
  simp[]
QED

(* Ref-level leaf-map adapter.  The declared-region equation explicitly ties
   the reference/key hash slot to the protected contract declaration. *)
Theorem current_declared_leaf_read_hashmap_typed:
  contract_storage_well_formed cx st /\
  declared_storage_region cx mid n [ValueSubscript kv] =
    SOME (b,hashmap_slot_for root_slot kt kv,tv) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  ?v. read_hashmap cx st (HashMapRef b root_slot kt (Type typ)) kv = SOME v /\
      value_has_type tv v
Proof
  rpt strip_tac >>
  `?v. read_storage_slot cx b (hashmap_slot_for root_slot kt kv) tv st =
         (INL v,st) /\ value_has_type tv v` by
    metis_tac[current_declared_storage_region_read_typed] >>
  Cases_on `decode_value (get_storage cx st b)
              (w2n (hashmap_slot_for root_slot kt kv)) tv` >>
  gvs[read_storage_slot_def, bind_def, lift_option_def, return_def, raise_def,
      get_storage_backend_eq, vyperHashMapTheory.read_hashmap_def,
      vyperHashMapStorageTheory.hashmap_read_def]
QED

(* A successful resolver walk stays inside the current encoded root. *)
Theorem resolve_array_element_current_region:
  !cx b base tv subs st tenv ty slot final_tv rsubs st'.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot,final_tv,rsubs),st') ==>
    slots_in_range (get_storage cx st' b) (w2n slot) final_tv
Proof
  (ho_match_mp_tac resolve_array_element_ind) >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >>
  imp_res_tac evaluate_type_ArrayTV_inv >>
  gvs[vyperTypingTheory.well_formed_type_value_def, get_storage_backend_eq]
  >- (`w2n (base' + n2w (Num idx * type_slot_size tv)) =
         w2n base' + Num idx * type_slot_size tv /\
       w2n base' <= w2n (base' + n2w (Num idx * type_slot_size tv)) /\
       w2n (base' + n2w (Num idx * type_slot_size tv)) +
         type_slot_size tv <=
         w2n base' + type_slot_size (ArrayTV tv (Fixed n)) /\
       w2n (base' + n2w (Num idx * type_slot_size tv)) +
         type_slot_size tv <= dimword(:256)` by
        (irule fixed_array_child_region_bounds >> simp[]) >>
      `slots_in_range (get_storage cx s'' b)
         (w2n base' + Num idx * type_slot_size tv) tv` by
        (irule static_slots_in_range_index >> qexists `n` >>
         gvs[slots_in_range_def]) >>
      qpat_assum `!elem_offset st tenv' ty slot' final_tv' rsubs' st'. _`
        (qspecl_then
          [`0`,`s''`,`tenv`,`elem_ty`,`slot`,`final_tv`,`rsubs`,`st'`] mp_tac) >>
      simp[])
  >- (`w2n (base' + n2w (1 + Num idx * type_slot_size tv)) =
         w2n base' + 1 + Num idx * type_slot_size tv /\
       w2n base' <=
         w2n (base' + n2w (1 + Num idx * type_slot_size tv)) /\
       w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
         type_slot_size tv <=
         w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) /\
       w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
         type_slot_size tv <= dimword(:256)` by
        (irule dynamic_array_child_region_bounds >> simp[]) >>
      `slots_in_range (get_storage cx s'' b)
         (w2n base' + 1 + Num idx * type_slot_size tv) tv` by
        (irule dyn_slots_in_range_index >>
         qexists `w2n (read_slot (get_storage cx s'' b) (w2n base'))` >>
         gvs[slots_in_range_def, vyperStorageTheory.read_slot_def] >>
         `MIN (w2n (lookup_storage base' (get_storage cx s'' b))) n =
          w2n (lookup_storage base' (get_storage cx s'' b))` by
           (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
         gvs[]) >>
      `base' + n2w (1 + Num idx * type_slot_size tv) =
       base' + n2w (Num idx * type_slot_size tv + 1)` by
        (AP_TERM_TAC >> AP_TERM_TAC >>
         MATCH_ACCEPT_TAC arithmeticTheory.ADD_COMM) >>
      qpat_x_assum
        `resolve_array_element cx b
           (base' + n2w (Num idx * type_slot_size tv + 1)) tv subs s'' = _`
        mp_tac >>
      qpat_x_assum
        `base' + n2w (1 + Num idx * type_slot_size tv) = _`
        (fn th => once_rewrite_tac [GSYM th]) >> strip_tac >>
      `type_slot_size tv +
         w2n (base' + n2w (1 + Num idx * type_slot_size tv)) <=
       dimword(:256)` by decide_tac >>
      `slots_in_range (get_storage cx s'' b)
         (w2n (base' + n2w (1 + Num idx * type_slot_size tv))) tv` by
        metis_tac[] >>
      qpat_assum `!elem_offset st tenv' ty slot' final_tv' rsubs' st'. _`
        (qspecl_then
          [`1`,`s''`,`tenv`,`elem_ty`,`slot`,`final_tv`,`rsubs`,`st'`] mp_tac) >>
      disch_then irule >> simp[])
QED

(* Exact slot/type boundary for the read and write paths selected by ArrayRef.
   The resolver consumes only leading array subscripts; [rsubs] records any
   remaining structural path to be handled by [assign_subscripts]. *)
Theorem current_arrayref_resolved_path_sound:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storage_var_info cx mid n = SOME (b,off,root_tv) /\
  resolve_array_element cx b (n2w off) root_tv subs st =
    (INL (slot,leaf_tv,rsubs),st_res) ==>
  leaf_type root_tv subs = leaf_type leaf_tv rsubs /\
  well_formed_type_value leaf_tv /\
  w2n ((n2w off):bytes32) <= w2n slot /\
  w2n slot + type_slot_size leaf_tv <=
    w2n ((n2w off):bytes32) + type_slot_size root_tv /\
  w2n slot + type_slot_size leaf_tv <= dimword(:256) /\
  slots_in_range (get_storage cx st_res b) (w2n slot) leaf_tv
Proof
  rpt strip_tac >>
  drule storage_var_info_components >> strip_tac >>
  `declared_storage_region cx mid n [] =
     SOME (b,n2w off,root_tv)` by
    metis_tac[declared_storage_region_ordinary] >>
  `w2n ((n2w off):bytes32) + type_slot_size root_tv <= dimword(:256)` by
    metis_tac[storage_layout_safe_region_nonoverflow] >>
  `get_storage_backend cx b st =
     (INL (get_storage cx st b),st)` by
    simp[get_storage_backend_eq] >>
  `slots_in_range (get_storage cx st b)
     (w2n ((n2w off):bytes32)) root_tv` by
    metis_tac[contract_storage_well_formed_region] >>
  `well_formed_type_value root_tv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `slots_in_range (get_storage cx st_res b) (w2n slot) leaf_tv` by
    (irule resolve_array_element_current_region >>
     qexistsl [`n2w off`,`rsubs`,`st`,`subs`,`get_tenv cx`,`root_tv`,`typ`] >>
     simp[]) >>
  metis_tac[resolve_array_element_leaf_type,
            resolve_array_element_preserves_well_formed_type,
            resolve_array_element_region_bounds]
QED

(* Exact current read at the region selected by an ArrayRef resolver walk. *)
Theorem current_arrayref_resolved_read_typed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storage_var_info cx mid n = SOME (b,off,root_tv) /\
  resolve_array_element cx b (n2w off) root_tv subs st =
    (INL (slot,leaf_tv,rsubs),st_res) ==>
  ?v. read_storage_slot cx b slot leaf_tv st_res = (INL v,st_res) /\
      value_has_type leaf_tv v
Proof
  rpt strip_tac >>
  drule_all current_arrayref_resolved_path_sound >> strip_tac >>
  `?v. decode_value (get_storage cx st_res b) (w2n slot) leaf_tv = SOME v /\
       value_has_type leaf_tv v` by
    metis_tac[decode_value_from_slots_in_range] >>
  qexists_tac `v` >>
  gvs[read_storage_slot_def, bind_def, lift_option_def, return_def,
      get_storage_backend_eq]
QED

(* When the resolver consumes the complete subscript path, expose the type in
   the caller's original path vocabulary.  This is the direct read adapter for
   nested indexed ArrayRef clients. *)
Theorem current_arrayref_resolved_leaf_read_typed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storage_var_info cx mid n = SOME (b,off,root_tv) /\
  resolve_array_element cx b (n2w off) root_tv subs st =
    (INL (slot,leaf_tv,[]),st_res) ==>
  ?v. read_storage_slot cx b slot leaf_tv st_res = (INL v,st_res) /\
      value_has_type (leaf_type root_tv subs) v
Proof
  rpt strip_tac >>
  drule_all current_arrayref_resolved_read_typed >>
  strip_tac >> qexists_tac `v` >> simp[] >>
  metis_tac[resolve_array_element_leaf_type, vyperTypingTheory.leaf_type_def]
QED

(* Type adapter used by the corresponding whole-leaf write path. *)
Theorem current_arrayref_resolved_leaf_write_value_typed:
  resolve_array_element cx b root_slot root_tv subs st =
    (INL (slot,leaf_tv,[]),st_res) /\
  value_has_type (leaf_type root_tv subs) v ==>
  value_has_type leaf_tv v
Proof
  metis_tac[resolve_array_element_leaf_type, vyperTypingTheory.leaf_type_def]
QED
val _ = export_theory();
