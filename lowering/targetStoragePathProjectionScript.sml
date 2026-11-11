Theory targetStoragePathProjection
Ancestors
  targetStorageProjectionFrame assignBasePtrStorageTaint
  vyperStorageLayoutSafety loweringStateRelDefs targetPlaceLive
  vyperStoragePlaceProvenance vyperInterpreter vyperState exprSimPopNestedBase
  allocLimits targetPlaceSim vyperTypeEnv stmtSimAssignAttr exprLowering
  targetEffectfulStorageHeader targetPlaceSimCasesBase stmtSimAugAssignPlaceStorage

Theorem storage_read_live_declared_relative_projection:
  !cx mid name keys tr root rtv slot tv st.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    storage_layout_safe cx /\ storage_read_live cx tr st slot tv ==>
    !j b. w2n slot <= j /\ j < w2n slot + type_slot_size tv /\
      dead_bytes st (w2n root) rtv j b ==>
      dead_bytes st (w2n slot) tv j b
Proof
  rpt strip_tac >>
  `storage_dead cx tr st j b` by
    (irule declared_region_dead_storage_dead >>
     qexistsl_tac [`root`, `mid`, `name`, `keys`, `rtv`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         `~((mid,name,keys) = (mid',n',subs'))` by
           (strip_tac >> gvs[]) >>
         drule_all storage_layout_safe_region_separation >> simp[]) >>
     drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  gvs[storage_read_live_def] >> metis_tac[]
QED

Theorem storage_read_live_capacity_frame:
  !cx mid name keys tr root rtv slot tv st st'.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    storage_layout_safe cx /\ storage_read_live cx tr st slot tv /\
    w2n root <= w2n slot /\
    w2n slot + type_slot_size tv <= w2n root + type_slot_size rtv /\
    (!q. w2n root <= q /\ q < w2n root + type_slot_size rtv ==>
      lookup_storage (n2w q) st' = lookup_storage (n2w q) st) ==>
    storage_read_live cx tr st' slot tv
Proof
  rpt strip_tac >> irule storage_projection_capacity_read_live >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`keys`, `mid`, `name`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule storage_read_live_declared_relative_projection >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all storage_layout_safe_region_nonoverflow >> simp[]
QED

(* A non-dynamic step selects the same fixed subregion in every backend.
   The backend at which the step ran need not be the one being projected. *)
Theorem storage_fixed_extension_read_live:
  !cx tr raw slot tv sb st tr' slot' tv' st'.
    storage_read_live cx tr raw slot tv /\
    (!et n. tv <> ArrayTV et (Dynamic n)) /\
    extend_storage_place cx tr slot tv sb st =
      (INL (StoragePlace tr' slot' tv'),st') ==>
    tr' = tr /\ storage_read_live cx tr raw slot' tv'
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `sb`)
  >- (Cases_on `tv` >>
      gvs[extend_storage_place_def, bind_def, ignore_bind_def,
          lift_option_type_def, check_def, assert_def, return_def, raise_def,
          AllCaseEqs(), vyperMiscTheory.option_CASE_rator,
          vyperMiscTheory.prod_CASE_rator] >>
      pairarg_tac >> gvs[return_def] >>
      irule accountsRelPropsTheory.storage_read_live_field >> metis_tac[]) >>
  Cases_on `v` >> Cases_on `tv` >>
  gvs[extend_storage_place_def, raise_def]
  >~ [`TupleTV tvs`]
  >- (gvs[bind_def, ignore_bind_def, lift_option_type_def, check_def,
          assert_def, return_def, raise_def, AllCaseEqs(),
          vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator] >>
      irule nested_pop_live_tuple_element >> metis_tac[]) >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >> gvs[] >>
  gvs[extend_storage_place_def, resolve_array_element_def, bind_def,
      ignore_bind_def, lift_option_type_def, check_def, assert_def,
      return_def, raise_def, AllCaseEqs(), resolve_array_element_empty,
      vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator] >>
  irule nested_pop_live_fixed_element >> metis_tac[]
QED

Theorem storage_fixed_extension_slots_in_range:
  !cx tr raw slot tv sb st tr' slot' tv' st'.
    slots_in_range raw (w2n slot) tv /\
    (!et n. tv <> ArrayTV et (Dynamic n)) /\
    extend_storage_place cx tr slot tv sb st =
      (INL (StoragePlace tr' slot' tv'),st') ==>
    tr' = tr /\ slots_in_range raw (w2n slot') tv'
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `sb`)
  >- (Cases_on `tv` >>
      gvs[extend_storage_place_def, bind_def, ignore_bind_def,
          lift_option_type_def, check_def, assert_def, return_def, raise_def,
          AllCaseEqs(), vyperMiscTheory.option_CASE_rator,
          vyperMiscTheory.prod_CASE_rator] >>
      pairarg_tac >> gvs[return_def] >>
      irule vyperLookupStorageTheory.storage_field_slots_in_range >> metis_tac[]) >>
  Cases_on `v` >> Cases_on `tv` >>
  gvs[extend_storage_place_def, raise_def]
  >~ [`TupleTV tvs`]
  >- (gvs[bind_def, ignore_bind_def, lift_option_type_def, check_def,
          assert_def, return_def, raise_def, AllCaseEqs(),
          vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator] >>
      irule nested_pop_tuple_slots >> metis_tac[]) >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >> gvs[] >>
  gvs[extend_storage_place_def, resolve_array_element_def, bind_def,
      ignore_bind_def, lift_option_type_def, check_def, assert_def,
      return_def, raise_def, AllCaseEqs(), resolve_array_element_empty,
      vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator] >>
  irule nested_pop_fixed_slots >> metis_tac[]
QED

Theorem typed_target_place_type:
  !bt cenv cx env es vt.
    expr_sim_inv cenv cx env es /\
    ~immutable_root cx bt /\ type_place_target env bt = SOME vt ==>
    target_place_type cenv bt = SOME (value_type_place vt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >>
  simp[type_place_target_NameTarget, type_place_target_TopLevelNameTarget,
       type_place_target_AttributeTarget, type_place_target_SubscriptTarget,
       target_place_type_def] >> rpt strip_tac >> gvs[]
  >~ [`cenv.ce_var_type id`]
  >- (gvs[exprSimHypsDefsTheory.expr_sim_inv_def, value_type_place_def])
  >~ [`cenv.ce_hashmap_info p`]
  >- (PairCases_on `p` >>
      `env_consistent env cx es` by
        fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
      gvs[immutable_root_def, target_root_def,
          type_place_target_TopLevelNameTarget]
      >- (fs[vyperTypeInvariantsTheory.env_consistent_def,
             vyperTypeInvariantsTheory.env_context_consistent_def] >>
          metis_tac[]) >>
      Cases_on `vt`
      >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
          gvs[exprSimHypsDefsTheory.expr_sim_inv_def, value_type_place_def] >>
          metis_tac[]) >>
      gvs[exprSimHypsDefsTheory.expr_sim_inv_def,
          placeTypingPropsTheory.place_map_tables_agree_on_defined_def] >>
      first_x_assum drule >> simp[value_type_place_def] >>
      Cases_on `cenv.ce_hashmap_info (p0,p1)` >> simp[] >>
      PairCases_on `x` >> simp[])
  >~ [`subscript_vtype vt' (expr_type e) = SOME vt`]
  >- (qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >> simp[] >>
      disch_then drule >>
      gvs[immutable_root_def, target_root_def] >>
      strip_tac >>
      Cases_on `vt'` >> gvs[value_type_place_def, vyperTypeSystemTheory.subscript_vtype_def] >>
      Cases_on `t` >> gvs[vyperTypeSystemTheory.subscript_vtype_def, value_type_place_def]) >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >> simp[] >>
  disch_then drule >> gvs[immutable_root_def, target_root_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  Cases_on `tgt_ty` >>
  gvs[vyperTypeSystemTheory.attribute_type_def, value_type_place_def] >>
  `attribute_type (get_tenv cx) (StructT p) s = SOME ty` by
    simp[vyperTypeSystemTheory.attribute_type_def] >>
  drule_all attribute_type_struct_field >> strip_tac >> simp[]
QED

(* Storage result types depend on the declared path, not on index effects. *)
Theorem eval_base_storage_type_alignment:
  !bt vt env cx st pv em.
    env_consistent env cx st /\ type_place_target env bt = SOME vt /\
    eval_base_place cx bt st = (INL pv,em) ==>
    case pv of
    | PlaceR (StoragePlace tr slot tv) =>
        ?ty. vt = Type ty /\ evaluate_type env.type_defs ty = SOME tv
    | HashMapRef tr slot kt leaf => vt = HashMapT kt leaf
    | _ => T
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >>
  simp[type_place_target_NameTarget, type_place_target_TopLevelNameTarget,
       type_place_target_AttributeTarget, type_place_target_SubscriptTarget,
       Once evaluate_def, bind_def, AllCaseEqs(), get_scopes_def,
       type_check_def, assert_def, ignore_bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
      drule_all vyperPlaceResultTypingTheory.lookup_global_target_success_typed >>
      strip_tac >> Cases_on `vt` >> Cases_on `pv` >>
      gvs[vyperTypeInvariantsTheory.eval_result_typed_def] >>
      Cases_on `p` >>
      gvs[vyperTypeInvariantsTheory.runtime_place_typed_def,
          place_type_value_def, return_def]) >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >> simp[] >>
  disch_then drule >> disch_then drule >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  Cases_on `pv'` >>
  gvs[extend_place_def, raise_def]
  >~ [`HashMapT t v`]
  >- (Cases_on `v` >>
      gvs[vyperTypeSystemTheory.subscript_vtype_def, bind_def,
          lift_option_type_def, return_def, raise_def, AllCaseEqs(),
          vyperMiscTheory.option_CASE_rator]) >>
  Cases_on `p` >>
  gvs[extend_place_def, extend_memory_place_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()]
  >~ [`subscript_vtype (Type ty) _ = SOME vt`]
  >- (Cases_on `ty` >>
      gvs[vyperTypeSystemTheory.subscript_vtype_def, vyperValueTheory.evaluate_type_def,
          AllCaseEqs()] >>
      rename1 `extend_storage_place _ _ _ _ (ValueSubscript key) _ = _` >>
      Cases_on `key` >>
      gvs[extend_storage_place_def, resolve_array_element_def, bind_def,
          ignore_bind_def, lift_option_type_def, check_def, assert_def,
          return_def, raise_def, resolve_array_element_empty,
          vyperMiscTheory.prod_CASE_rator, AllCaseEqs()]) >>
  drule_all vyperPlaceResultTypingTheory.attribute_type_runtime_step >> strip_tac >>
  Cases_on `t` >>
  gvs[extend_storage_place_def, subscript_type_def, bind_def,
      lift_option_type_def, ignore_bind_def, return_def, raise_def,
      vyperMiscTheory.prod_CASE_rator, AllCaseEqs()] >>
  drule vyperPlaceResultTypingTheory.struct_field_slot_exists >> strip_tac >>
  gvs[return_def, raise_def]
QED

Theorem target_pre_storage_type_alignment:
  !cenv cx env bt st vt tr slot tv em.
    target_pre cenv cx env bt st /\
    type_place_target env bt = SOME vt /\
    eval_base_place cx bt st = (INL (PlaceR (StoragePlace tr slot tv)),em) ==>
    ?ty. vt = Type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
      target_place_type cenv bt = SOME (ValPT ty)
Proof
  rpt strip_tac >>
  fs[target_pre_def] >>
  `env_consistent env cx st` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all eval_base_storage_type_alignment >> simp[] >> strip_tac >>
  drule_all typed_target_place_type >>
  gvs[value_type_place_def, vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_context_consistent_def]
QED

Theorem target_no_dynamic_storage_projection:
  !bt tops ctx cenv cx env st vt tr slot tv em now.
    body_inv tops ctx cenv cx /\ target_pre cenv cx env bt st /\
    type_place_target env bt = SOME vt /\ ~target_through_dynarray cenv bt /\
    eval_base_place cx bt st = (INL (PlaceR (StoragePlace tr slot tv)),em) /\
    expr_sim_inv cenv cx env now ==>
    storage_read_live cx tr (get_storage cx now tr) slot tv /\
    slots_in_range (get_storage cx now tr) (w2n slot) tv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >>
  simp[type_place_target_NameTarget, type_place_target_TopLevelNameTarget,
       type_place_target_AttributeTarget, type_place_target_SubscriptTarget,
       target_through_dynarray_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
      drule lookup_global_storage_region >> strip_tac >>
      conj_tac
      >- (irule accountsRelPropsTheory.declared_storage_region_read_live >>
          goal_assum (drule_at Any)) >>
      irule declared_region_post_index_slots >> conj_tac
      >- (goal_assum (drule_at Any)) >>
      fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `target_pre cenv cx env b st` by metis_tac[target_pre_sub] >>
  Cases_on `pv` >> gvs[extend_place_def, raise_def]
  >~ [`HashMapRef b' c t v`]
  >- (drule eval_base_place_region >>
      simp[storage_result_region_def, storage_mapping_region_def] >> strip_tac >>
      Cases_on `v` >>
      gvs[extend_place_def, bind_def, lift_option_type_def, return_def,
          raise_def, AllCaseEqs(), vyperMiscTheory.option_CASE_rator] >>
      rename1 `hashmap_slot c (encode_hashmap_key t key)` >>
      qpat_x_assum `!subs leaf_slot leaf_tv.
        resolve_hashmap_leaf _ _ _ subs = SOME (leaf_slot,leaf_tv) ==> _`
        (qspec_then `[ValueSubscript key]` mp_tac) >>
      simp[resolve_hashmap_leaf_def, subscript_to_value_def] >> strip_tac >>
      conj_tac
      >- (irule accountsRelPropsTheory.declared_storage_region_read_live >>
          goal_assum (drule_at Any)) >>
      irule declared_region_post_index_slots >> conj_tac
      >- (goal_assum (drule_at Any)) >>
      fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  Cases_on `p` >>
  gvs[extend_memory_place_def, extend_place_def, bind_def, return_def,
      raise_def, ignore_bind_def, AllCaseEqs()] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_all target_pre_storage_type_alignment >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME t` >>
  `!et n. t <> ArrayTV et (Dynamic n)` by
    (Cases_on `ann` >>
     gvs[vyperTypeSystemTheory.subscript_vtype_def,
         vyperTypeSystemTheory.attribute_type_def,
         vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rename1 `~(case bd of Fixed _ => F | Dynamic _ => T)` >>
     Cases_on `bd` >> gvs[]) >>
  drule_all storage_fixed_extension_read_live >> strip_tac >> gvs[] >>
  drule_all storage_fixed_extension_slots_in_range >> simp[]
QED

Theorem storage_saved_place_capacity_frame:
  !cx mid name keys tr root rtv path delta slot tv raw raw'.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    storage_layout_safe cx /\ storage_subregion rtv path delta tv /\
    slot = root + n2w delta /\ 0 < type_slot_size tv /\
    storage_read_live cx tr raw slot tv /\ slots_in_range raw (w2n slot) tv /\
    (!q. w2n root <= q /\ q < w2n root + type_slot_size rtv ==>
      lookup_storage (n2w q) raw' = lookup_storage (n2w q) raw) ==>
    storage_read_live cx tr raw' slot tv /\ slots_in_range raw' (w2n slot) tv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all storage_layout_safe_region_nonoverflow >> strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `delta < dimword (:256)` by decide_tac >>
  `w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n slot = w2n root + delta` by
    (gvs[] >> simp[wordsTheory.w2n_add_2]) >>
  conj_tac
  >- (irule storage_read_live_capacity_frame >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`keys`, `mid`, `name`] >> simp[] >>
      qexists_tac `raw` >> gvs[]) >>
  irule (iffRL (INST_TYPE [alpha |-> ``:256``] slots_in_range_capacity_frame)) >>
  goal_assum (drule_at Any) >>
  qexists_tac `raw` >> simp[] >> decide_tac
QED

Theorem target_storage_resolution_capacity_frame:
  !bt tops ctx cenv cx env st vt tr slot tv em.
    body_inv tops ctx cenv cx /\ target_pre cenv cx env bt st /\
    type_place_target env bt = SOME vt /\
    eval_base_place cx bt st = (INL (PlaceR (StoragePlace tr slot tv)),em) /\
    (!b ix s0 pv sm ev se value sf mid name keys tr0 root rtv.
      RTC (\u v. (?fld. v = AttributeTarget u fld) \/
                  (?ix. v = SubscriptTarget u ix)) (SubscriptTarget b ix) bt /\
      target_through_dynarray cenv b /\
      target_pre cenv cx env (SubscriptTarget b ix) s0 /\
      (?vty. type_place_target env (SubscriptTarget b ix) = SOME vty) /\
      eval_base_place cx b s0 = (INL pv,sm) /\
      eval_expr cx ix sm = (INL ev,se) /\
      read_result cx ev se = (INL value,sf) /\
      declared_storage_region cx mid name keys = SOME (tr0,root,rtv) /\
      (?leaf off path delta. pv = PlaceR (StoragePlace tr0 off leaf) /\
        storage_subregion rtv path delta leaf /\ off = root + n2w delta) ==>
      !q. w2n root <= q /\ q < w2n root + type_slot_size rtv ==>
        lookup_storage (n2w q) (get_storage cx sf tr0) =
        lookup_storage (n2w q) (get_storage cx sm tr0)) ==>
    storage_read_live cx tr (get_storage cx em tr) slot tv /\
    slots_in_range (get_storage cx em tr) (w2n slot) tv
Proof
  measureInduct_on `base_assignment_target_size bt` >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env em` by metis_tac[eval_base_place_sim_inv] >>
  reverse (Cases_on `target_through_dynarray cenv bt`)
  >- (irule target_no_dynamic_storage_projection >> metis_tac[]) >>
  Cases_on `bt` >>
  gvs[target_through_dynarray_def, type_place_target_AttributeTarget,
      type_place_target_SubscriptTarget, Once evaluate_def, bind_def,
      AllCaseEqs(), return_def, raise_def] >>
  `target_pre cenv cx env b st` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env s''` by metis_tac[eval_base_place_sim_inv] >>
  Cases_on `pv` >> gvs[extend_place_def, raise_def]
  >>~- ([`HashMapRef b' c t v`],
      drule eval_base_place_region >>
      simp[storage_result_region_def, storage_mapping_region_def] >> strip_tac >>
      Cases_on `v` >>
      gvs[extend_place_def, bind_def, lift_option_type_def, return_def,
          raise_def, AllCaseEqs(), vyperMiscTheory.option_CASE_rator] >>
      rename1 `hashmap_slot c (encode_hashmap_key t key)` >>
      qpat_x_assum `!subs leaf_slot leaf_tv.
        resolve_hashmap_leaf _ _ _ subs = SOME (leaf_slot,leaf_tv) ==> _`
        (qspec_then `[ValueSubscript key]` mp_tac) >>
      simp[resolve_hashmap_leaf_def, subscript_to_value_def] >> strip_tac >>
      conj_tac
      >- (irule accountsRelPropsTheory.declared_storage_region_read_live >>
          goal_assum (drule_at Any)) >>
      irule declared_region_post_index_slots >> conj_tac
      >- (goal_assum (drule_at Any)) >>
      fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  Cases_on `p` >>
  gvs[extend_memory_place_def, extend_place_def, bind_def, return_def,
      raise_def, ignore_bind_def, AllCaseEqs()] >>
  rename1 `extend_storage_place cx base_tr base_slot base_tv sb sf =
    (INL (StoragePlace tr slot tv),em)` >>
  qpat_x_assum `!y. base_assignment_target_size y < _ ==> _`
    (qspec_then `b` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `eval_base_place _ _ _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `target_pre _ _ _ _ _`)) >> simp[] >>
  (impl_tac
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
       first_x_assum irule >>
       simp[] >>
       goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
       goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
       goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
       simp[] >> conj_tac >- metis_tac[] >>
       simp[relationTheory.RTC_RULES_RIGHT1])) >>
  strip_tac >>
  drule vyperPlaceFramesTheory.extend_storage_place_state >> strip_tac >> gvs[]
  >~ [`target_pre cenv cx env (AttributeTarget b s) st`]
  >- (drule_all aug_place_storage_extend_live_all >> strip_tac >> gvs[] >>
      drule_all aug_place_storage_extend_range >> simp[]) >>
  `storage_read_live cx base_tr (get_storage cx em base_tr) base_slot base_tv /\
   slots_in_range (get_storage cx em base_tr) (w2n base_slot) base_tv` by
    (Cases_on `type_slot_size base_tv = 0`
     >- (conj_tac
         >- (simp[storage_read_live_def] >>
             metis_tac[wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
         irule (cj 1 vyperLookupStorageTheory.slots_in_range_zero_reads) >> simp[]) >>
     Cases_on `target_through_dynarray cenv b`
     >- (drule eval_base_place_region >>
         simp[storage_result_region_def, storage_place_region_def] >> strip_tac >>
         irule storage_saved_place_capacity_frame >>
         conj_tac >- fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> simp[] >>
         goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> simp[] >>
         qexists_tac `get_storage cx s'' base_tr` >> simp[] >>
         rpt strip_tac >>
         qpat_x_assum `!b' ix s0 pv' sm ev se value sf mid name keys tr0 root rtv. _`
           (qspecl_then [`b`,`e`] mp_tac) >>
         disch_then (drule_at (Pat `eval_base_place _ _ _ = _`)) >>
         disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
         disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
         disch_then (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
         simp[relationTheory.RTC_REFL] >> metis_tac[]) >>
     irule target_no_dynamic_storage_projection >> metis_tac[]) >>
  drule_all aug_place_storage_extend_live_all >> strip_tac >> gvs[] >>
  drule_all aug_place_storage_extend_range >> simp[]
QED
