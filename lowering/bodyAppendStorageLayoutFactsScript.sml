(* Source target metadata for aggregate storage Append. *)
Theory bodyAppendStorageLayoutFacts
Ancestors
  bodyInvCodeProps bodyInvSplit bodyStorageMetadata exprBodyPreProps moduleVariableKeyProps alist
  bodyAppendStorageFacts whitelistVisibility exprSimHyps valueEncodingProps
  bodySim vyperValue

Theorem append_aggregate_target_layout_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  supported_variable_decl tops (NONE,id) =
    SOME (vis,mut,ArrayT elem (Dynamic dn),SOME slot) /\
  (mut = Storage \/ mut = Transient) /\
  expr_sim_inv_mods mods cenv cx env es /\
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
      (INL (StoragePlace (mut = Transient) (n2w rslot) (ArrayTV tv (Dynamic dn))),
       es with storage_trace := es.storage_trace ++
         [StorageRoot (mut = Transient) rslot (ArrayTV tv (Dynamic dn))])
Proof
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `get_module_code cx src = SOME tops` by metis_tac[contract_inv_module_codes] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[contract_inv_unqualified_variable_keys] >>
  drule_all supported_variable_decl_storage_binding >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_then strip_assume_tac append_typing_target >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all append_typed_storage_target >> strip_tac >> gvs[] >>
  drule_all append_storage_target_eval >> strip_tac >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv elem = type_memory_size tv'` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >> metis_tac[]) >>
  simp[type_memory_size_slots]
QED

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
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `src = NONE` by metis_tac[supported_variable_decl_mem] >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  drule_then assume_tac body_inv_contract >>
  drule_then strip_assume_tac body_inv_main_code >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_split_def] >>
  irule (SIMP_RULE (srw_ss()) [ALOOKUP_def]
    (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `exps` |-> `[]`]
      (SPEC_ALL append_aggregate_target_layout_mods))) >> simp[] >> metis_tac[]
QED
