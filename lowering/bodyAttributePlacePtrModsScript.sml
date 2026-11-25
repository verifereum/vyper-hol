(* The selected place retains the base place's backing storage or owner. *)
Theory bodyAttributePlacePtrMods
Ancestors
  bodyFullPostsMods exprSimAttributeFields exprSimFieldLayout exprSimProps
  exprSimAttributeProps exprBodyPreProps exprSimHypsDefs vyperTypeEvalCaseProofs
  vyperTypeInvariants vyperPlaceResultTyping vyperState compileEnv context
  loweringPosts venomState finite_map words list

Theorem attribute_memory_root_type[local]:
  expr_sim_inv_mods mods cenv cx env t /\
  lookup_scopes id t.scopes = SOME entry /\ cenv.ce_var_type id = SOME ty ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  fs[env_consistent_def, env_scopes_consistent_def] >>
  `?ty'. FLOOKUP env.var_types id = SOME ty'` by
    (qpat_x_assum `!id e. lookup_scopes _ _ = SOME _ ==> IS_SOME _`
       drule >> simp[optionTheory.IS_SOME_EXISTS]) >>
  `cenv.ce_var_type id = SOME ty'` by fs[expr_sim_inv_mods_def] >>
  metis_tac[]
QED

Theorem attribute_field_place_ptr_mods:
  expr_sim_inv_mods mods cenv cx env t /\
  eval_result_typed (env,cx,t) r (Type (StructT sid)) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
  ALOOKUP fs fld = SOME ftv /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  (!ty op. bvv = StackValue ty op ==> !pl. r <> PlaceR pl) /\
  select_result cx (StructT sid) r (AttrSubscript fld) ee = (INL tv',ee') /\
  vv_place_ptr_mods cenv cx ee q r bvv /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) ==>
  vv_place_ptr_mods cenv cx ee q tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv)))
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  Cases_on `r` >> gvs[eval_result_typed_def]
  >- (gvs[select_result_def, bind_def, return_def, lift_option_type_def,
          lift_sum_def, raise_def, AllCaseEqs(), vv_place_ptr_mods_def, vv_place_ptr_def]) >>
  rename1 `PlaceR pl` >> Cases_on `bvv` >> gvs[vv_loc_def, vv_location_def, vv_operand_def] >>
  Cases_on `pl`
  >- suspend "storage"
  >- suspend "memory" >>
  suspend "immutable"
QED

Resume attribute_field_place_ptr_mods[storage]:
  rename1 `StoragePlace tr slot tv` >>
  `tv = StructTV fs` by fs[runtime_place_typed_def, place_type_value_def, return_def] >>
  drule_then strip_assume_tac vyperPlaceResultTypingTheory.struct_field_slot_exists >>
  drule_all_then assume_tac struct_field_offset_slots_eq >>
  gvs[select_result_def, extend_place_def, extend_storage_place_def,
      bind_def, return_def, lift_option_type_def, vv_place_ptr_mods_def, vv_place_ptr_def] >>
  Cases_on `tr` >> gvs[slot_loc_def, attr_offset_def, mk_ptr_def]
QED

Resume attribute_field_place_ptr_mods[memory]:
  rename1 `MemoryPlace id path` >>
  `tv' = PlaceR (MemoryPlace id (path ++ [AttrSubscript fld]))` by
    (drule_then (qspecl_then [`id`,`path ++ [AttrSubscript fld]`] mp_tac)
       select_result_memory_place >> simp[]) >>
  `?entry. lookup_scopes id t.scopes = SOME entry /\
           subscripts_type entry.type path = SOME (StructTV fs)` by
    (qpat_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `lookup_scopes id t.scopes` >>
     gvs[runtime_place_typed_def, place_type_value_def, get_scopes_def,
         bind_def, lift_option_type_def, return_def, raise_def] >>
     rename1 `lookup_scopes id t.scopes = SOME entry` >>
     Cases_on `subscripts_type entry.type path` >> gvs[return_def, raise_def]) >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, attr_offset_def, mk_ptr_def] >>
  drule_all_then assume_tac attribute_memory_root_type >>
  drule_then strip_assume_tac mem_path_offset_sound >> gvs[] >>
  drule_all_then assume_tac mem_field_offset_layout >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
   SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld,ftv)`
    by simp[mem_step_offset_def] >>
  drule_all_then assume_tac mem_path_offset_snoc >>
  simp[GSYM WORD_ADD_ASSOC, word_add_n2w]
QED

Resume attribute_field_place_ptr_mods[immutable]:
  rename1 `ImmutablePlace owner id path` >>
  `tv' = PlaceR (ImmutablePlace owner id (path ++ [AttrSubscript fld]))` by
    gvs[select_result_def, extend_place_def, bind_def, return_def,
        lift_sum_def, raise_def, ignore_bind_def, AllCaseEqs(), extend_memory_place_def] >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, attr_offset_def, mk_ptr_def] >>
  `subscripts_type itv path = SOME (StructTV fs)` by
    (qpat_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `ALOOKUP t.immutables cx.txn.target` >>
     gvs[runtime_place_typed_def, place_type_value_def, get_immutables_def,
         get_address_immutables_def, bind_def, lift_option_type_def, return_def, raise_def] >>
     Cases_on `subscripts_type itv path` >> gvs[return_def, raise_def]) >>
  drule_then strip_assume_tac mem_path_offset_sound >> gvs[] >>
  drule_all_then assume_tac mem_field_offset_layout >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
   SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld,ftv)`
    by simp[mem_step_offset_def] >>
  drule_all_then assume_tac mem_path_offset_snoc >>
  simp[word_add_n2w]
QED

Finalise attribute_field_place_ptr_mods
