(* Declaration and layout boundary for aggregate storage Append. *)
Theory bodyAppendAggregateMetadata
Ancestors
  bodyAppendStorageFacts exprSimHypsDefs vyperTypeEnv vyperValue
  vyperStorageLayoutSafety vyperAST

Theorem body_append_aggregate_metadata_ptr:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) =
    SOME (vis,mut,ArrayT elem (Dynamic dn),SOME declared_slot) /\
  (mut = Storage \/ mut = Transient) /\ ~supported_full_word_type elem /\
  supported_stmt tops bindings (Append (TopLevelNameTarget (src,id)) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget (src,id)) e) ==>
  src = NONE /\ expr_type e = elem /\ ~is_word_type elem /\
  cenv.ce_module_var_type (src,id) = SOME (ArrayT elem (Dynamic dn)) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_dynarray_capacity (src,id) = dn /\
  ?tr key slot tv.
    get_module_code cx src = SOME tops /\
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl tr (ArrayT elem (Dynamic dn)),key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) elem = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) (ArrayTV tv (Dynamic dn))),es) /\
    type_memory_bytes cenv elem = 32 * type_slot_size tv /\
    type_memory_bytes cenv elem < 2 ** 64 /\
    0 < dn /\ dn + 1 < dimword(:256) /\ 0 < type_slot_size tv /\
    type_slot_size (ArrayTV tv (Dynamic dn)) < dimword(:256) /\
    declared_storage_region cx src id [] =
      SOME (tr,n2w slot,ArrayTV tv (Dynamic dn)) /\
    w2n (n2w slot : bytes32) + type_slot_size (ArrayTV tv (Dynamic dn)) <=
      dimword(:256) /\
    (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
      FLOOKUP cenv.ce_module_vars (src,id) =
        SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot)))
Proof
  strip_tac >>
  mp_tac (Q.INST [`cap` |-> `dn`, `ast_slot` |-> `declared_slot`]
    (SPEC_ALL bodyAppendStorageFactsTheory.body_append_aggregate_metadata)) >>
  simp[] >> strip_tac >>
  drule append_typing_target >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_all append_typed_storage_target >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv (expr_type e) < 2 ** 64` by
    (drule body_append_element_alloc_bound >> simp[]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  drule_all storage_layout_safe_region_nonoverflow >> strip_tac >>
  gvs[type_slot_size_def, bound_length_def] >>
  `cenv.ce_module_dynarray_capacity (NONE,id) <=
   cenv.ce_module_dynarray_capacity (NONE,id) * type_slot_size tv` by simp[] >>
  decide_tac
QED
