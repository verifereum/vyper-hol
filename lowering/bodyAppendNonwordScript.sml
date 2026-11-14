(* S1 cases for Append to a local, subscript or attribute target whose element
   is not a full word (struct, tuple, array, bytes, string, or a narrow word).

   The lowering resolves the target's array pointer (compile_get_target_ptr),
   lowers the element, stages a non-word element through a fresh buffer with
   compile_store_memory (relayout from the lowered type to the array's element
   type), then appends it (compile_dynarray_append): compile_store_memory into a
   memory array, compile_store_slots into a storage or transient array.

   body_append_nonword_local: the target's root is a local, so the array is in
   memory.  The element type comes from the typing (type_place_target); the
   gate's bindings-based target info isn't tied to it, so the element may be
   wider than expr_type e.

   body_append_nonword_nested: the root is a top-level storage or transient
   variable, below a subscript or attribute.  The gate's target info is then
   computed from the module's declarations, so the element type is exactly
   expr_type e.

   With the full-word case (stmtSimAppendResolved) these partition the
   non-top-level Append targets of body_append_case. *)
Theory bodyAppendNonword
Ancestors
  bodySim targetPlaceSim supportedTypes bodyAppendNestedPre bodyAppendNestedEndpoint
  bodyAugPlaceTarget stmtSimAppendNestedAggregate bodyAppendResolvedPre
  supportedStmts supportedTargets vyperTypeSystem vyperTypeCallGraph exprSimHypsDefs

Theorem body_append_nonword_local:
  !cx bt e.
    (!s'' p t'. eval_target_place cx bt s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx bt /\
    (?id. target_root bt = NameTarget id) /\
    ~supported_full_word_type (expr_type e) ==>
    body_stmt_ok cx (Append bt e)
Proof
  cheat
QED

Theorem body_append_nonword_nested:
  !cx bt e.
    (!s'' p t'. eval_target_place cx bt s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx bt /\
    (!id. bt <> TopLevelNameTarget id) /\
    (?id. target_root bt = TopLevelNameTarget id) /\
    ~supported_full_word_type (expr_type e) ==>
    body_stmt_ok cx (Append bt e)
Proof
  rpt gen_tac >> strip_tac >> rw[body_stmt_ok_def] >>
  mp_tac (SPEC_ALL body_append_nested_aggregate_metadata) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `target_sim ctx func cenv cx env bt es` by
    metis_tac[aug_place_body_target_sim] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[int_calls_stmt_def] >>
     metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]) >>
  `well_typed_target env bt (ArrayT (expr_type e) (Dynamic cap))` by
    simp[well_typed_target_def] >>
  `?pt. supported_target_info tops bindings bt = SOME pt` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  irule compile_append_nested_aggregate_stmt_frag >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cap`, `env`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_append_nested_rhs_endpoint >> strip_tac >> simp[] >>
  mp_tac (Q.INST [`elem` |-> `expr_type e`]
    (SPEC_ALL body_append_nested_storage_endpoint)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]
QED
