(* Preconditions for aggregate Append below a declared storage root. *)
Theory bodyAppendNestedPre
Ancestors
  bodyAppendResolvedPre bodyTargetInfoTyping targetStorageDomain bodyAppendStorageFacts
  bodySim supportedStmts supportedTypes supportedTargets exprSimHypsDefs
  exprSimHyps valueEncodingProps
  vyperTypeSystem targetPlaceSim exprLowering

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
