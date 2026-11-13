(* Probe the proposed semantic-purity adapter before using same-state geometry. *)
Theory tuplePlacePointerReady
Ancestors
  supportedTargets targetPlaceLive vyperPureExpr tuplePlaceReachable tuplePlaceHead
  bodySimAugPlaceStore tupleMemoryLayout tuplePlaceZero tuplePlaceBounds
  aggregateEvaluatedLayout bodyMemoryDefs

Theorem tuple_place_supported_gas_index_not_semantic_pure:
  supported_target_pure tops
    (SubscriptTarget (NameTarget "a") (Builtin (BaseT (UintT 256)) (Env MsgGas) [])) /\
  ~EVERY pure_expr (target_indices
    (SubscriptTarget (NameTarget "a") (Builtin (BaseT (UintT 256)) (Env MsgGas) [])))
Proof
  EVAL_TAC
QED

(* Actual evaluation may change gas and other non-scope state. *)
Theorem tuple_place_base_target_transition:
  eval_base_place cx bt es = (INL (PlaceR p),ee) ==>
  eval_target_place cx bt es = (INL p,ee)
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_place_def, vyperStateTheory.return_def]
QED

Theorem tuple_place_target_endpoint_writable:
  expr_sim_inv cenv cx env es /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) ==>
  writable_place_result cx ee (PlaceR p)
Proof
  rpt strip_tac >>
  drule tuple_place_base_target_transition >> strip_tac >>
  gvs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all exprSimPopNestedLocalSourceTheory.eval_target_place_writable >> simp[]
QED

Theorem tuple_place_head_pointer_operands:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  i <= j /\ j < LENGTH ltys ==>
  ?v. eval_operand (EL j elems) s = SOME v /\
    if is_word_type (EL j ltys) then
      v = typed_val_to_w256 (EL j ltvs) (EL j vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))
Proof
  strip_tac >> fs[tuple_place_head_def] >>
  `MEM (EL j elems) elems` by (irule listTheory.EL_MEM >> simp[]) >>
  `?x. EL j elems = Var x` by gvs[listTheory.EVERY_MEM] >>
  `?v. eval_operand (EL j elems) s0 = SOME v /\
       if is_word_type (EL j ltys) then
         v = typed_val_to_w256 (EL j ltvs) (EL j vs)
       else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))` by
    (qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `j` mp_tac) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists `v` >> conj_tac
  >- (irule tuplePlaceSnapshotTheory.tuple_place_target_operand >>
      conj_tac >- simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[]
QED


Theorem tuple_place_pointer_local_regions:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sp /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s ==>
  (!n b sz. local_region cenv ee.scopes s n b sz <=>
            local_region cenv es.scopes s0 n b sz)
Proof
  strip_tac >>
  drule_all tuplePlaceBorrowTheory.tuple_place_pure_target_scopes >> strip_tac >>
  drule tuplePlaceSnapshotTheory.tuple_place_target_frame >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by simp[] >>
  drule_all wordArgsPtrTheory.wb_frame_local_regions >> metis_tac[]
QED

Theorem tuple_place_pointer_snapshot:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) ==>
  tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s
Proof
  strip_tac >>
  `sp.cs_next_id <= sa.cs_next_id` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!n b sz. local_region cenv ee.scopes s n b sz <=>
             local_region cenv es.scopes s0 n b sz` by
    (irule tuple_place_pointer_local_regions >>
     fs[tuple_place_head_def] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[tuple_place_head_def, tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      fs[loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  qexistsl [`n`, `b`, `sz`] >> simp[]
QED

Theorem tuple_place_pointer_pending_memory:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory
Proof
  strip_tac >> fs[tuple_place_head_def] >>
  `val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s0.vs_memory` by
    simp[] >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (irule aug_place_tuple_wf_project >>
     gvs[vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tuple_element_interval >> simp[]) >>
  `mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory =
   mem_bytes_at (w2n w) (type_memory_size_list ltvs) s0.vs_memory` by
    (fs[tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
     >- gvs[listTheory.EVERY_EL]
     >- simp[valueEncodingDefsTheory.mem_bytes_at_def]
     >- (drule_all tuplePlaceSnapshotTheory.tuple_place_target_allocation >>
         strip_tac >> drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`w2n w-b`, `type_memory_size_list ltvs`] mp_tac) >>
         simp[]) >>
     drule_all tuplePlaceBorrowTheory.tuple_place_pure_target_borrow_bytes >>
     strip_tac >> drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`w2n w-b`, `type_memory_size_list ltvs`] mp_tac) >>
     simp[]) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >> qexistsl [`type_memory_size (EL j ltvs)`, `s0.vs_memory`] >> simp[] >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then
    [`SUM (MAP type_memory_size (TAKE j ltvs))`, `type_memory_size (EL j ltvs)`]
    mp_tac) >> simp[]
QED

Theorem tuple_place_index_fit:
  arg_types_fit ltys tys /\
  evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type tenv (TupleT ltys) = SOME (TupleTV ltvs) /\ i < LENGTH tys ==>
  arg_type_fits (EL i ltys) (EL i tys) /\
  (is_word_type (EL i ltys) <=> is_word_type (EL i tys))
Proof
  strip_tac >>
  `arg_type_fits (TupleT ltys) (TupleT tys)` by
    simp[vyperTypeSystemTheory.arg_type_fits_def] >>
  drule_all typedCopyCompatibilityPtrTheory.arg_type_fits_tuple_layouts >>
  strip_tac >> gvs[] >>
  `arg_type_fits (EL i ltys) (EL i tys)` by simp[] >>
  simp[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]
QED

Theorem tuple_place_index_sizes:
  assignable_type tenv (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type tenv (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs) + 64 < dimword (:256) /\
    type_memory_size (EL j ltvs) + 64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  i < LENGTH tys /\ ~is_word_type (EL i ltys) ==>
  0 < type_memory_size (EL i tvs) /\
  0 < type_memory_size (EL i ltvs) /\
  type_memory_size (EL i tvs) + 64 < dimword (:256) /\
  type_memory_size (EL i ltvs) + 64 < dimword (:256) /\
  cenv.ce_target CapMcopy
Proof
  strip_tac >>
  drule_all tuple_place_index_fit >> strip_tac >>
  drule_all tuplePlaceZeroTheory.tuple_place_element_source_positive >> strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `0 < type_memory_size (EL i tvs)` by
    (first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
     qspec_then `EL i tvs` mp_tac exprSimFieldLayoutTheory.slot_count_of_memory_size >>
     Cases_on `type_memory_size (EL i tvs) = 0` >> simp[]) >>
  `EXISTS (\t. ~is_word_type t) ltys` by
    (simp[listTheory.EXISTS_MEM] >> qexists `EL i ltys` >> simp[] >>
     gvs[listTheory.EL_MEM]) >>
  gvs[]
QED

Theorem tuple_place_snapshot_element_bounds:
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s /\
  stmt_state_rel ctx func cenv cx es s /\ LENGTH ltvs = LENGTH ltys /\
  i < LENGTH ltys /\ ~is_word_type (EL i ltys) /\
  0 < type_memory_size (EL i ltvs) ==>
  w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
    type_memory_size (EL i ltvs) < dimword (:256) /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      lo <= aid /\ aid < hi /\
      b <= w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) /\
      w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
        type_memory_size (EL i ltvs) <= b+sz /\
      (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) \/
   (?n b sz. ltys = tys /\ local_region cenv es.scopes s n b sz /\
      b <= w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) /\
      w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
        type_memory_size (EL i ltvs) <= b+sz /\
      local_path_at cenv cx n (w2n w-b) (TupleTV ltvs)))
Proof
  strip_tac >>
  `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tuple_element_interval >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     irule exprLoweringPropsTheory.alloca_room_next_lt >> metis_tac[]) >>
  fs[tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
  >- gvs[listTheory.EVERY_EL]
  >- (`b+sz <= s.vs_alloca_next` by
        (fs[exprLoweringPropsTheory.stmt_state_rel_def,
            venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
      conj_tac >- decide_tac >> disj1_tac >>
      qexistsl [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]) >>
  `b+sz <= s.vs_alloca_next` by
    (irule bodyMemoryDefsTheory.body_local_region_frontier >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac >- decide_tac >> disj2_tac >>
  qexistsl [`n`, `b`, `sz`] >> simp[] >> decide_tac
QED

Theorem tuple_place_writable_borrow_destination_apart:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  local_region cenv ee.scopes s n b sz /\
  local_path_at cenv cx n k (TupleTV tvs) /\
  k + type_memory_size (TupleTV tvs) <= sz /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ writable_place_result cx ee (PlaceR p) /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) ==>
  b + k + type_memory_size (TupleTV tvs) <= w2n dw \/
  w2n dw + type_memory_size (EL i tvs) <= b + k
Proof
  rpt strip_tac >> Cases_on `p` >>
  gvs[loweringPostsTheory.place_ptr_rel_def, loweringPostsTheory.slot_loc_def, AllCaseEqs(),
      vyperTargetPlaceWriteTheory.writable_place_result_def,
      vyperPlaceWriteSoundnessTheory.runtime_place_writable_def] >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace s' l)) (b' + n2w k')
     (SOME LocMemory) (Type (EL i tys))` by
    (simp[loweringPostsTheory.place_ptr_rel_def] >> metis_tac[]) >>
  drule_all tuple_place_memory_coordinates >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\ i < LENGTH tvs` by
    (gvs[vyperValueTheory.evaluate_type_def,
         vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
     drule exprSimAttributeFieldsTheory.opt_mmap_el >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  gvs[] >> reverse (Cases_on `s' = n`)
  >- (`regions_disjoint b sz base' sz''` by
        (gvs[exprLoweringPropsTheory.stmt_state_rel_def,
             loweringStateRelDefsTheory.state_rel_def, loweringStateRelDefsTheory.local_ptrs_rel_def] >>
         metis_tac[]) >>
      gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  gvs[loweringStateRelDefsTheory.local_region_def, loweringPostsTheory.local_path_at_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  `tuple_place_no_tuple_step entry.type l` by
    (irule tuple_place_mutable_path_barrier >> metis_tac[]) >>
  irule tuplePlaceGeometryTheory.tuple_place_tuple_barrier_apart >>
  conj_tac >- metis_tac[listTheory.EL_MEM] >>
  qexistsl [`path`, `l`, `entry.type`] >> simp[]
QED

(* Reassemble the value relation after pointer evaluation, at its actual endpoint. *)
Theorem tuple_place_pointer_value_rel:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
  i < LENGTH ltys ==>
  expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s
Proof
  strip_tac >>
  `?v. eval_operand (EL i elems) s = SOME v /\
    if is_word_type (EL i ltys) then
      v = typed_val_to_w256 (EL i ltvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    (irule tuple_place_head_pointer_operands >>
     qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any)) >>
  simp[loweringPostsTheory.expr_val_rel_def] >>
  Cases_on `is_word_type (EL i ltys)` >- gvs[] >>
  gvs[] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule tuple_place_pointer_pending_memory >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem tuple_place_pointer_source_facts:
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) ==>
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env ee` by
    (irule targetPlaceSimCasesBaseTheory.eval_base_place_sim_inv >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `storage_place_region cx p` by
    (drule tuple_place_base_target_transition >>
     metis_tac[vyperStoragePlaceProvenanceTheory.eval_target_place_region]) >>
  simp[] >> rpt strip_tac >>
  irule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem tuple_place_pointer_element_facts:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  i < LENGTH ltys ==>
  value_has_type (EL i ltvs) (EL i vs) /\
  (!x. EL i elems = Var x ==> not_fresh_at sa x)
Proof
  strip_tac >>
  `ci_mono sp sa` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >> simp[]) >>
  fs[tuple_place_head_def, vyperTypeDefaultsTheory.values_have_types_LIST_REL,
     listTheory.LIST_REL_EL_EQN] >>
  rpt strip_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
  goal_assum (drule_at Any) >>
  `MEM (EL i elems) elems` by (irule listTheory.EL_MEM >> simp[]) >> metis_tac[]
QED

Theorem tuple_place_pointer_owned_region:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sp.cs_next_id /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b)
Proof
  strip_tac >>
  `!n lb lsz. local_region cenv ee.scopes s n lb lsz <=>
    local_region cenv es.scopes s0 n lb lsz` by
    (irule tuple_place_pointer_local_regions >>
     fs[tuple_place_head_def] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `sp.cs_next_id <= sa.cs_next_id` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  fs[loweringPostsTheory.target_post_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
