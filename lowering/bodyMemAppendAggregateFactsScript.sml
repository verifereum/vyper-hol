(* Body boundaries for aggregate storage Append. *)
Theory bodyMemAppendAggregateFacts
Ancestors
  bodyAppendStorageAdapter bodyAppendStorageFacts bodyMemAssignTopCopyFacts
  supportedStmts supportedExprs loweringPosts exprSimMemDefs
  valueEncodingProps vyperAST bodySim bodyStorageMetadata supportedProgram
  supportedDecls supportedTypes compileEnv exprSimHyps whitelistVisibility
  vyperValue vyperTypeValues

Theorem append_narrow_annotation:
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  supported_variable_decl tops nid =
    SOME (vis, mut, ArrayT elem (Dynamic dn), SOME slot) /\
  ~supported_full_word_type elem ==> expr_type e = elem
Proof
  strip_tac >>
  `~supported_storage_dynamic_array tops nid` by
    (strip_tac >> drule supported_append_storage_decl >> strip_tac >> gvs[]) >>
  gvs[supported_stmt_def]
QED

Theorem append_pure_post_type:
  supported_pure_expr tops e ==> post_value_type cenv e = expr_type e
Proof
  strip_tac >> irule post_value_type_not_int_call >>
  rpt strip_tac >> gvs[supported_pure_expr_def]
QED

Theorem append_aggregate_rhs_memory:
  supported_pure_expr tops e /\
  expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  expr_store_bound cx (expr_type e) v op s ==>
  ?w. eval_operand op s = SOME w /\
    val_in_memory tv v (w2n w) s.vs_memory /\
    (type_slot_size tv = 0 \/
     w2n w + 32 * type_slot_size tv <= s.vs_alloca_next)
Proof
  strip_tac >> drule append_pure_post_type >> strip_tac >>
  `expr_val_rel cx (expr_type e) v op s` by fs[expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  drule_all topcopy_val_store_size >> strip_tac >>
  gvs[expr_store_bound_def, type_memory_size_slots]
QED

Theorem append_storage_element_domain:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops nid =
    SOME (vis,mut,ArrayT elem (Dynamic dn),SOME slot) /\
  (mut = Storage \/ mut = Transient) ==>
  supported_storage_type tops elem /\ ~is_bytestring_type elem /\
  (~supported_full_word_type elem ==> ~is_word_type elem)
Proof
  Cases_on `nid` >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `supported_program tops` by fs[body_inv_def] >>
  drule_all supported_program_declaration >> strip_tac >>
  `supported_storage_type tops elem` by
    (Cases_on `vis` >>
     gvs[supported_declaration_header_def, supported_storage_array_depth]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `supported_storage_type _ _` mp_tac >>
      Cases_on `elem` >> simp[is_bytestring_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[is_bytestring_type_def, supported_storage_type_def,
           Once supported_nested_type_def, supported_full_word_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      simp[is_bytestring_type_def, supported_storage_type_def,
           Once supported_nested_type_def, supported_full_word_type_def]) >>
  Cases_on `elem` >>
  gvs[supported_storage_type_def, Once supported_nested_type_def,
      supported_full_word_type_def, is_word_type_def, is_bytestring_type_def]
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
