Theory targetStoragePathProjection
Ancestors
  targetStorageProjectionFrame assignBasePtrStorageTaint
  vyperStorageLayoutSafety loweringStateRelDefs targetPlaceLive
  vyperStoragePlaceProvenance vyperInterpreter vyperState exprSimPopNestedBase
  allocLimits targetPlaceSim vyperTypeEnv stmtSimAssignAttr exprLowering

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
