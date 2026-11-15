(* Source target metadata for aggregate storage Append. *)
Theory bodyAppendStorageLayoutFacts
Ancestors
  bodyAppendStorageFacts whitelistVisibility exprSimHyps valueEncodingProps
  bodySim vyperValue

Theorem append_aggregate_target_layout:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) =
    SOME (vis,mut,ArrayT elem (Dynamic dn),SOME slot) /\
  (mut = Storage \/ mut = Transient) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' ==>
  ?tv rslot.
    evaluate_type (get_tenv cx) elem = SOME tv /\
    type_memory_bytes cenv elem = 32 * type_slot_size tv /\
    0 < dn /\ 0 < type_slot_size tv /\
    type_slot_size (ArrayTV tv (Dynamic dn)) < dimword (:256) /\
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl (mut = Transient) (ArrayT elem (Dynamic dn)),id) /\
    lookup_var_slot_from_layout cx (mut = Transient) src id = SOME rslot /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace (mut = Transient) (n2w rslot)
        (ArrayTV tv (Dynamic dn))),
       es with storage_trace := es.storage_trace ++
         [StorageRoot (mut = Transient) rslot (ArrayTV tv (Dynamic dn))])
Proof
  strip_tac >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  drule supported_variable_decl_storage_binding >> disch_then drule >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_all append_typed_storage_target >> strip_tac >> gvs[] >>
  drule_all append_storage_target_eval >> strip_tac >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[type_memory_size_slots]
QED
