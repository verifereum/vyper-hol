(* Preconditions for aggregate Append below a declared storage root. *)
Theory bodyAppendNestedPre
Ancestors
  bodyAppendResolvedPre bodyTargetInfoTyping targetStorageDomain bodyAppendStorageFacts
  bodySim supportedStmts supportedTypes supportedTargets exprSimHypsDefs
  exprSimHyps valueEncodingProps
  vyperTypeSystem targetPlaceSim exprLowering bodyAppendStorageAdapter
  vyperTypeInvariants bodyExprPreFacts loweringPosts vyperTypeCallGraph
  targetSubscriptSplit vyperState vyperValue vyperAST

Theorem body_append_nested_aggregate_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Append bt e) /\
  ~(?id. bt = TopLevelNameTarget id) /\
  (?id. target_root bt = TopLevelNameTarget id) /\
  ~supported_full_word_type (expr_type e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append bt e) = SOME env' /\
  stmt_exprs_ok cenv (Append bt e) /\
  call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append bt e) ==> occurs_abi_decode_target target tops) ==>
  target_pre cenv cx env bt es /\ expr_body_pre cenv cx env e es /\
  supported_storage_type tops (expr_type e) /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_memory_bytes cenv (expr_type e) < 2 ** 64 /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
        type_memory_bytes cenv (expr_type e) = 32 * type_slot_size tv) /\
  ?cap. type_place_target env bt =
    SOME (Type (ArrayT (expr_type e) (Dynamic cap)))
Proof
  strip_tac >>
  drule_all body_append_target_rhs_pre >> strip_tac >>
  `?cap. supported_target_info tops bindings bt =
    SOME (ValPT (ArrayT (expr_type e) (Dynamic cap)))` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  pop_assum strip_assume_tac >>
  drule append_typing_target >> strip_tac >>
  drule_all supported_target_info_typing >> simp[] >> strip_tac >> gvs[] >>
  `supported_program tops` by gvs[body_inv_def] >>
  drule_all supported_target_storage_domain >> simp[] >> strip_tac >>
  `supported_storage_type tops (expr_type e)` by
    gvs[supported_storage_array_depth] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    (qpat_x_assum `supported_storage_type _ _` mp_tac >>
     Cases_on `expr_type e` >>
     simp[compileEnvTheory.is_word_type_def,
          compileEnvTheory.is_bytestring_type_def,
          supported_storage_type_def, Once supported_nested_type_def,
          supported_full_word_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >>
     simp[compileEnvTheory.is_word_type_def,
          compileEnvTheory.is_bytestring_type_def,
          supported_storage_type_def, Once supported_nested_type_def] >>
     metis_tac[]) >>
  drule body_append_element_alloc_bound >> strip_tac >>
  simp[] >> (conj_tac >- gvs[]) >> rpt strip_tac >>
  drule_all expr_sim_inv_memory_size >>
  simp[type_memory_size_slots]
QED

Theorem body_append_nested_aggregate_metadata:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Append bt e) /\
  ~(?id. bt = TopLevelNameTarget id) /\
  (?id. target_root bt = TopLevelNameTarget id) /\
  ~supported_full_word_type (expr_type e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append bt e) = SOME env' /\
  stmt_exprs_ok cenv (Append bt e) /\
  call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append bt e) ==> occurs_abi_decode_target target tops) ==>
  target_pre cenv cx env bt es /\ expr_body_pre cenv cx env e es /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  lowered_value_type cenv e = expr_type e /\ post_value_type cenv e = expr_type e /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  ?cap tv. type_place_target env bt =
      SOME (Type (ArrayT (expr_type e) (Dynamic cap))) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    0 < type_slot_size tv /\ cap < dimword (:256) /\
    type_memory_bytes cenv (expr_type e) = 32 * type_slot_size tv /\
    type_memory_bytes cenv (expr_type e) < dimword (:256)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL body_append_nested_aggregate_pre) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule append_typing_target >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `0 < type_slot_size tv` by metis_tac[assignable_type_slot_size_pos] >>
  `supported_pure_expr tops e` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[bodyAppendStorageAdapterTheory.append_aggregate_lowered_type] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_not_int_call >> rpt strip_tac >> gvs[int_calls_expr_def]) >>
  `well_formed_vtype (get_tenv cx) (Type (ArrayT (expr_type e) (Dynamic cap)))` by
    metis_tac[target_subscript_pre_result_well_formed] >>
  `cap < dimword (:256)` by
    (gvs[well_formed_vtype_def, well_formed_type_def, evaluate_type_def,
         bound_length_def, AllCaseEqs(), type_slot_size_def] >>
     Cases_on `type_slot_size tv` >> gvs[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  simp[] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> first_assum ACCEPT_TAC) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  fs[wordsTheory.dimword_def] >> decide_tac
QED
