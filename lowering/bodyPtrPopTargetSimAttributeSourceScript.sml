Theory bodyPtrPopTargetSimAttributeSource
Ancestors
  bodyPtrPopTargetDefs targetPlaceSimCasesBase stmtSimAssignAttr
  stmtSimAssignAttrStorage exprSimAttributeFields exprSimFieldLayout
  exprSimHypsDefs loweringPosts compileEnv vyperInterpreter vyperState
  vyperPlaceTyping vyperPlaceResultTyping vyperTypeSystem vyperValue
  words exprLowering exprSimProps

Theorem target_field_source_ptr:
  expr_sim_inv cenv cx env es /\
  place_ptr_rel cenv cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
  SND (SND rb) = SOME (ValPT (StructT sid)) /\
  place_readable cx es pv /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
  extend_place cx pv (AttrSubscript fld) es = (res,ee) /\
  (!m. res <> INR (Error (TypeError m))) ==>
  ee = es /\
  ?pv'. res = INL pv' /\ place_readable cx es pv' /\
    target_field_type cenv (SND (SND rb)) fld =
      SOME (value_type_place (Type fty)) /\
    place_ptr_rel cenv cx t pv'
      (w0 + n2w (target_field_offset cenv (FST (SND rb)) (SND (SND rb)) fld))
      (FST (SND rb)) (Type fty) /\
    (!gs. extend_place cx pv (AttrSubscript fld) (es with gas_obs := gs) =
      (INL pv',es with gas_obs := gs)) /\
    (!G tn. target_ptr_ok cenv pv rb G tn t ==>
            target_ptr_ok cenv pv' rb G tn t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all stmtSimAssignAttrTheory.attribute_type_struct_field >> strip_tac >>
  `target_field_type cenv (SND (SND rb)) fld =
     SOME (value_type_place (Type fty))` by
    simp[target_field_type_def, value_type_place_def] >>
  simp[] >>
  Cases_on `pv` >> gvs[place_ptr_rel_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[place_ptr_rel_def]
  >- suspend "storage" >> suspend "memory"
QED

Resume target_field_source_ptr[storage]:
  rename1 `StoragePlace tr slot tv` >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, bind_def] >>
  Cases_on `extend_storage_place cx tr slot (StructTV fs) (AttrSubscript fld) es` >>
  rename1 `(r1,es1)` >> strip_tac >>
  `!m. r1 <> INR (Error (TypeError m))` by (rpt strip_tac >> gvs[]) >>
  drule_all stmtSimAssignAttrStorageTheory.extend_storage_place_attr >>
  strip_tac >> gvs[return_def] >>
  drule struct_field_slot_type >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  Cases_on `tr` >>
  simp[target_field_offset_def, slot_loc_def, place_readable_def,
       place_ptr_rel_def, target_ptr_ok_def, extend_place_def,
       extend_storage_place_def, bind_def, lift_option_type_def, return_def]
QED

Resume target_field_source_ptr[memory]:
  rename1 `MemoryPlace id path` >>
  `popped_keys_indexed es.scopes` by fs[expr_sim_inv_def] >>
  drule_all extend_place_memory_attr >> strip_tac >> gvs[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  drule_all mem_field_offset_layout >> strip_tac >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
     SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields
             (nsid_to_string sid)) fld,ftv)` by simp[mem_step_offset_def] >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  simp[target_field_offset_def, place_ptr_rel_def, target_ptr_ok_def,
       GSYM word_add_n2w, WORD_ADD_ASSOC] >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, return_def, lift_sum_def,
       extend_memory_place_def, ignore_bind_def] >>
  Cases_on `lookup_scopes id ee.scopes` >>
  simp[raise_def, return_def] >>
  rename1 `lookup_scopes id ee.scopes = SOME entry` >>
  Cases_on `subscripts_type entry.type path` >>
  simp[raise_def, return_def] >>
  rename1 `subscripts_type entry.type path = SOME ptv` >>
  Cases_on `read_memory_path entry path` >>
  simp[raise_def, return_def] >>
  rename1 `read_memory_path entry path = INL current` >>
  Cases_on `evaluate_subscripts ptv current [AttrSubscript fld]` >>
  simp[raise_def, return_def]
QED

Finalise target_field_source_ptr
