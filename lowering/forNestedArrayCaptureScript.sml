(* Classify the result captured by a nested global For iterator. *)
Theory forNestedArrayCapture
Ancestors
  bodySim bodyStorageMetadata whitelistVisibility targetPlaceSim
  exprSimSource exprBodyPreProps vyperPlaceResultTyping vyperPlaceTyping
  vyperStoragePlaceProvenance vyperBareGlobalName vyperTypeValues vyperTyping
  vyperInterpreter vyperState vyperAST vyperTypeSystem list
  vyperTypeContract[qualified,ignore_grammar]

Theorem subscript_capture_step[local]:
  eval_expr cx (Subscript ann obj idx) es = (INL r,ee) ==>
  ?base mid raw v u. eval_expr cx obj es = (INL base,mid) /\
    (raw = base \/ (?w. raw = Value w)) /\
    select_result cx (expr_type obj) raw (ValueSubscript v) u = (INL r,ee)
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  qpat_x_assum `(if subscript_reads_base _ _ _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem select_capture_value[local]:
  select_result cx ty (Value v) sb s = (INL r,t) ==> ?w. r = Value w
Proof
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem select_capture_slot[local]:
  select_result cx ty raw sb s = (INL r,t) /\
  ((?tr loc tv. raw = PlaceR (StoragePlace tr loc tv)) \/
   (?tr loc kt vt. raw = HashMapRef tr loc kt vt) \/ (?v. raw = Value v)) ==>
  (?tr loc tv. r = PlaceR (StoragePlace tr loc tv)) \/
  (?tr loc kt vt. r = HashMapRef tr loc kt vt) \/ (?v. r = Value v)
Proof
  rpt strip_tac >> gvs[]
  >- (gvs[select_result_def, extend_place_def, bind_def, return_def, AllCaseEqs()] >>
      drule extend_storage_place_subregion >> strip_tac >> simp[])
  >- (Cases_on `sb` >> Cases_on `vt` >>
      gvs[select_result_def, extend_place_def, bind_def, ignore_bind_def,
          record_storage_event_def, lift_option_type_def, return_def,
          raise_def, AllCaseEqs()] >> metis_tac[]) >>
  drule select_capture_value >> metis_tac[]
QED

Theorem global_capture_slot[local]:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name name tops = SOME (decl,key) /\
  lookup_global cx src name s = (INL r,t) ==>
  (?tr loc tv. r = PlaceR (StoragePlace tr loc tv)) \/
  (?tr loc kt vt. r = HashMapRef tr loc kt vt)
Proof
  strip_tac >> Cases_on `decl` >>
  gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def,
      lift_option_type_def, return_def, raise_def, AllCaseEqs(),
      vyperMiscTheory.option_CASE_rator] >> metis_tac[]
QED

Theorem nested_slot_capture[local]:
  !e tgt cx src name es r ee.
    loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget (src,name) /\
    get_module_code cx src = SOME tops /\
    find_var_decl_by_name name tops = SOME (decl,key) /\
    eval_expr cx e es = (INL r,ee) ==>
    (?tr loc tv. r = PlaceR (StoragePlace tr loc tv)) \/
    (?tr loc kt vt. r = HashMapRef tr loc kt vt) \/ (?v. r = Value v)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def, AllCaseEqs()] >>
  rpt strip_tac
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule_all global_capture_slot >> metis_tac[])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs(), target_root_def] >>
      qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
      first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >>
      strip_tac >> irule select_capture_slot >> metis_tac[]) >>
  gvs[target_root_def] >> drule subscript_capture_step >> strip_tac >>
  qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
  first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >>
  strip_tac >> irule select_capture_slot >> metis_tac[]
QED

Theorem global_capture_immutable[local]:
  get_module_code cx src = SOME tops /\ find_var_decl_by_name name tops = NONE /\
  lookup_global cx src name s = (INL r,t) ==>
  r = PlaceR (ImmutablePlace src name []) /\
  ?tv a. lookup_immutable cx t src name = SOME (tv,a)
Proof
  strip_tac >> Cases_on `ALOOKUP s.immutables cx.txn.target` >>
  gvs[lookup_global_def, get_immutables_def, get_address_immutables_def,
      lookup_immutable_def, bind_def, lift_option_type_def, return_def,
      raise_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs(),
      pairTheory.EXISTS_PROD]
QED

(* Selection validates the extended path in the state after the index, not
   in the state at which its base pointer was captured. *)
Theorem select_capture_immutable[local]:
  select_result cx ty (PlaceR (ImmutablePlace src name path)) sb s = (INL r,t) ==>
  r = PlaceR (ImmutablePlace src name (path ++ [sb])) /\
  ?tv a w. lookup_immutable cx t src name = SOME (tv,a) /\
           evaluate_subscripts tv a (path ++ [sb]) = INL w
Proof
  Cases_on `ALOOKUP s.immutables cx.txn.target` >>
  simp[select_result_def, extend_place_def, extend_memory_place_def,
       place_type_value_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator] >>
  rename1 `ALOOKUP s.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) name` >> simp[] >>
  rename1 `FLOOKUP (get_source_immutables src imms) name = SOME tva` >>
  Cases_on `subscripts_type (FST tva) path` >> simp[] >>
  rename1 `subscripts_type (FST tva) path = SOME ptv` >>
  Cases_on `evaluate_subscripts (FST tva) (SND tva) path` >> simp[] >>
  rename1 `evaluate_subscripts (FST tva) (SND tva) path = INL v` >>
  Cases_on `evaluate_subscripts ptv v [sb]` >> simp[] >>
  strip_tac >> gvs[] >>
  drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` assume_tac) >>
  qexistsl [`FST tva`,`SND tva`] >> simp[lookup_immutable_def]
QED

Theorem nested_immutable_capture[local]:
  !e tgt cx src name es r ee.
    loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget (src,name) /\
    get_module_code cx src = SOME tops /\ find_var_decl_by_name name tops = NONE /\
    eval_expr cx e es = (INL r,ee) ==>
    (?v. r = Value v) \/
    ?path attrs tail tv a w.
      r = PlaceR (ImmutablePlace src name path) /\
      lookup_immutable cx ee src name = SOME (tv,a) /\
      evaluate_subscripts tv a path = INL w /\ path = MAP AttrSubscript attrs ++ tail /\
      (tail = [] \/ ?ix rest. tail = ValueSubscript ix :: rest) /\
      !extra. place_access tgt extra =
        (TopLevelNameTarget (src,name), if tail = [] then attrs ++ extra else attrs)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def, AllCaseEqs()] >>
  rpt strip_tac
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule_all global_capture_immutable >> strip_tac >>
      disj2_tac >> qexistsl [`[]`,`[]`,`tv`,`a`,`a`] >>
      simp[evaluate_subscripts_def, place_access_def])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs(), target_root_def] >>
      qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
      first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >>
      disch_then drule_all >> strip_tac >> gvs[]
      >- (drule select_capture_value >> simp[]) >>
      drule select_capture_immutable >> strip_tac >> gvs[] >>
      qmatch_asmsub_rename_tac `AttrSubscript att` >>
      qmatch_asmsub_rename_tac `MAP AttrSubscript attrs`
      >- (qexistsl [`attrs ++ [att]`,`[]`] >>
          gvs[place_access_def, MAP_APPEND, APPEND_ASSOC] >> metis_tac[]) >>
      qmatch_asmsub_rename_tac `ValueSubscript ix :: rest` >>
      qexistsl [`attrs`,`ValueSubscript ix :: (rest ++ [AttrSubscript att])`] >>
      simp[place_access_def, rich_listTheory.APPEND_ASSOC_CONS] >>
      metis_tac[listTheory.APPEND_ASSOC, APPEND]) >>
  gvs[target_root_def] >> drule subscript_capture_step >> strip_tac >> gvs[]
  >- (qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
      first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >>
      disch_then drule_all >> strip_tac >> gvs[]
      >- (drule select_capture_value >> simp[]) >>
      drule select_capture_immutable >> strip_tac >> gvs[] >>
      qmatch_asmsub_rename_tac `select_result _ _ _ (ValueSubscript ixnew) _` >>
      qmatch_asmsub_rename_tac `MAP AttrSubscript attrs`
      >- (qexistsl [`attrs`,`[ValueSubscript ixnew]`] >>
          simp[place_access_def] >> metis_tac[]) >>
      qmatch_asmsub_rename_tac `MAP AttrSubscript attrs ++ (ValueSubscript i0 :: rest)` >>
      qexistsl [`attrs`,`ValueSubscript i0 :: (rest ++ [ValueSubscript ixnew])`] >>
      simp[place_access_def, rich_listTheory.APPEND_ASSOC_CONS] >>
      metis_tac[listTheory.APPEND_ASSOC, APPEND]) >>
  drule select_capture_value >> simp[]
QED

Theorem iterator_attr_prefix_array[local]:
  !attrs tv a tail av.
    evaluate_subscripts tv a (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
    (tail = [] \/ ?ix rest. tail = ValueSubscript ix :: rest) ==>
    ?av'. evaluate_subscripts tv a (MAP AttrSubscript attrs) = INL (ArrayV av')
Proof
  Induct >> rpt gen_tac
  >- (simp[] >> rpt strip_tac
      >- gvs[evaluate_subscripts_def] >>
      Cases_on `ix` >> Cases_on `a` >> gvs[evaluate_subscripts_def]) >>
  Cases_on `a` >> simp[Once evaluate_subscripts_def] >> rpt strip_tac >>
  gvs[Once evaluate_subscripts_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem array_capture_typed[local]:
  expr_body_pre cenv cx env e es /\ expr_type e = ArrayT ty bd /\
  eval_expr cx e es = (INL r,ee) ==>
  ?elem. evaluate_type (get_tenv cx) ty = SOME elem /\
    evaluate_type env.type_defs (ArrayT ty bd) = SOME (ArrayTV elem bd) /\
    eval_result_typed (env,cx,ee) r (Type (ArrayT ty bd)) /\
    !v. read_result cx r ee = (INL v,ee) ==> ?av. v = ArrayV av
Proof
  strip_tac >> drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule expr_body_pre_env_type_defs >> strip_tac >> gvs[] >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  first_x_assum drule >> Cases_on `v` >> simp[value_has_type_inv]
QED

(* Reading an immutable place is reading its root and then the path. *)
Theorem read_result_immutable_place:
  read_result cx (PlaceR (ImmutablePlace src name path)) es = (INL v,es) <=>
  ?tv root. lookup_immutable cx es src name = SOME (tv,root) /\
            evaluate_subscripts tv root path = INL v
Proof
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, lookup_immutable_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) name` >>
  simp[AllCaseEqs(), return_def, raise_def] >>
  rename1 `FLOOKUP (get_source_immutables src imms) name = SOME tvroot` >>
  PairCases_on `tvroot` >>
  Cases_on `evaluate_subscripts tvroot0 tvroot1 path` >> simp[return_def,raise_def]
QED
(* A type-correct capture is either a copied array or a location in the
   declared root's region. In the immutable case the exposed prefix ends
   just before the first index (or at the array itself). *)
Theorem nested_array_capture_cases:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  expr_type e = ArrayT ty bd /\
  loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
  eval_expr cx e es = (INL r,ee) ==>
  ?elem. evaluate_type (get_tenv cx) ty = SOME elem /\
    (((?vis kind rt slot. supported_variable_decl tops nid = SOME (vis,kind,rt,SOME slot) /\
                           (kind = Storage \/ kind = Transient)) \/
      (?vis tr kt vt slot. supported_hashmap_decl tops nid = SOME (vis,tr,kt,vt,SOME slot))) ==>
      (?av. r = Value (ArrayV av)) \/
      (?tr loc. r = PlaceR (StoragePlace tr loc (ArrayTV elem bd)))) /\
    (IS_SOME (supported_immutable_type tops nid) ==>
      (?av. r = Value (ArrayV av)) \/
      ?src name path attrs tail rt rv av pav.
        nid = (src,name) /\ r = PlaceR (ImmutablePlace src name path) /\
        runtime_place_typed cx ee (ImmutablePlace src name path) (ArrayTV elem bd) /\
        place_access tgt [] = (TopLevelNameTarget nid,attrs) /\
        path = MAP AttrSubscript attrs ++ tail /\
        lookup_immutable cx ee src name = SOME (rt,rv) /\
        evaluate_subscripts rt rv (MAP AttrSubscript attrs) = INL (ArrayV pav) /\
        evaluate_subscripts rt rv path = INL (ArrayV av))
Proof
  strip_tac >> PairCases_on `nid` >>
  drule_all array_capture_typed >> strip_tac >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    fs[body_inv_def] >>
  qexists_tac `elem` >> simp[] >> conj_tac
  >- (strip_tac >>
      `nid0 = NONE /\ ?decl key. find_var_decl_by_name nid1 tops = SOME (decl,key)` by
        metis_tac[supported_variable_decl_storage_binding,
                  supported_hashmap_decl_storage_binding] >>
      gvs[] >> drule_all nested_slot_capture >> strip_tac >>
      gvs[vyperTypeInvariantsTheory.eval_result_typed_def, read_result_def, return_def]) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule_all supported_immutable_type_find_NONE >> strip_tac >> gvs[] >>
  drule_all nested_immutable_capture >> strip_tac
  >- gvs[read_result_def, return_def] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] (iffRL read_result_immutable_place)) >>
  strip_tac >>
  qpat_x_assum `r = PlaceR _` SUBST_ALL_TAC >>
  qpat_x_assum `!v. read_result _ _ _ = _ ==> _` drule >> strip_tac >>
  `?pav. evaluate_subscripts tv a (MAP AttrSubscript attrs) = INL (ArrayV pav)` by
    (irule iterator_attr_prefix_array >> metis_tac[]) >>
  disj2_tac >> qexistsl [`attrs`,`tail`,`tv`,`a`] >> gvs[] >> metis_tac[]
QED
