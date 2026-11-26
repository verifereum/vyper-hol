(* Tuple selection preserves the backing place and its linked owner. *)
Theory bodySubscriptTuplePlacePtrMods
Ancestors
  bodyFullPostsMods exprSimTuple exprSimAttributeProps exprSimProps
  exprBodyPreProps exprSimHypsDefs vyperTypeEvalCaseProofs vyperPlaceTyping
  vyperTypeInvariants vyperState compileEnv context loweringPosts venomState
  finite_map words list

Theorem tuple_memory_root_type[local]:
  expr_sim_inv_mods mods cenv cx env et /\
  lookup_scopes id et.scopes = SOME entry /\ cenv.ce_var_type id = SOME ty ==>
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

(* Use offsets at the original compile environment even when the
   pointer relation itself is interpreted for an imported owner. *)
Theorem tuple_subscript_place_ptr_mods:
  expr_sim_inv_mods mods cenv cx env et /\
  eval_result_typed (env,cx,et) raw (Type (TupleT tys)) /\
  ee.scopes = et.scopes /\ ee.immutables = et.immutables /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\
  (!ty op. bvv = StackValue ty op ==> !pl. raw <> PlaceR pl) /\
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee =
    (INL raw',ee) /\
  vv_place_ptr_mods cenv cx ee t raw bvv /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
  ((vv_loc bvv = LocMemory \/ vv_loc bvv = LocCode) ==>
    mem_step_offset (TupleTV tvs) (ValueSubscript (IntV (&k))) =
      SOME (tuple_offset cenv tys (vv_loc bvv) k,EL k tvs)) /\
  (!tr. vv_loc bvv = slot_loc tr ==>
    tuple_offset cenv tys (vv_loc bvv) k = tuple_prefix_slot_size k tvs) ==>
  vv_place_ptr_mods cenv cx ee t raw'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv)))
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  Cases_on `raw` >> gvs[eval_result_typed_def]
  >- gvs[select_result_def, bind_def, return_def, lift_option_type_def,
         lift_sum_def, raise_def, AllCaseEqs(), vv_place_ptr_mods_def, vv_place_ptr_def] >>
  rename1 `PlaceR pl` >> Cases_on `bvv` >> gvs[vv_loc_def, vv_location_def, vv_operand_def] >>
  Cases_on `pl`
  >- suspend "storage"
  >- suspend "memory" >>
  suspend "immutable"
QED

Resume tuple_subscript_place_ptr_mods[storage]:
  rename1 `StoragePlace tr slot tv` >>
  `tv = TupleTV tvs` by fs[runtime_place_typed_def, place_type_value_def, return_def] >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def] >>
  gvs[select_result_def, extend_place_def, extend_storage_place_def,
      bind_def, ignore_bind_def, check_def, assert_def, return_def,
      lift_option_type_def, listTheory.oEL_THM] >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def]
QED

Resume tuple_subscript_place_ptr_mods[memory]:
  rename1 `MemoryPlace id path` >>
  `raw' = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV (&k))]))` by
    (drule_then (qspecl_then [`id`,`path ++ [ValueSubscript (IntV (&k))]`] mp_tac)
       select_result_memory_place >> simp[]) >>
  fs[runtime_place_typed_memory] >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >>
  drule_all_then assume_tac tuple_memory_root_type >>
  drule_then strip_assume_tac mem_path_offset_sound >> gvs[] >>
  drule_all_then assume_tac mem_path_offset_snoc >>
  simp[GSYM WORD_ADD_ASSOC, word_add_n2w]
QED

Resume tuple_subscript_place_ptr_mods[immutable]:
  rename1 `ImmutablePlace owner id path` >>
  `raw' = PlaceR (ImmutablePlace owner id (path ++ [ValueSubscript (IntV (&k))]))` by
    gvs[select_result_def, extend_place_def, bind_def, return_def,
        lift_sum_def, raise_def, ignore_bind_def, AllCaseEqs(), extend_memory_place_def] >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >>
  `subscripts_type itv path = SOME (TupleTV tvs)` by
    (qpat_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `ALOOKUP et.immutables cx.txn.target` >>
     gvs[runtime_place_typed_def, place_type_value_def, get_immutables_def,
         get_address_immutables_def, bind_def, lift_option_type_def, return_def, raise_def] >>
     Cases_on `subscripts_type itv path` >> gvs[return_def, raise_def]) >>
  drule_then strip_assume_tac mem_path_offset_sound >> gvs[] >>
  drule_all_then assume_tac mem_path_offset_snoc >>
  simp[word_add_n2w]
QED

Finalise tuple_subscript_place_ptr_mods
