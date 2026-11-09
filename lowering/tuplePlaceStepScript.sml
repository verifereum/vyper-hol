(* Consume store frames at the single correctness endpoint. *)
Theory tuplePlaceStep
Ancestors
  tuplePlaceHeadAdvance vyperScopePreservation

Theorem tuple_place_endpoint_local_regions_some:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv cs /\
  (!x v. not_fresh_at cs x /\ lookup_var x s = SOME v ==>
    lookup_var x t = SOME v) /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  (!n b sz. local_region cenv es'.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz)
Proof
  strip_tac >> rpt gen_tac >> eq_tac
  >- (strip_tac >> irule exprSimPropsTheory.local_region_frame >>
      fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
      metis_tac[]) >>
  strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >> metis_tac[]
QED

Theorem tuple_place_head_advance_some:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s /\
  i < LENGTH ltys /\ sp.cs_next_var <= sb.cs_next_var /\
  sp.cs_next_id <= sb.cs_next_id /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region cenv ff.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  (!x v. not_fresh_at sp x /\ lookup_var x s = SOME v ==>
    lookup_var x t = SOME v) /\
  stmt_state_rel ctx func cenv cx ff t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!j. SUC i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
    val_in_memory (EL j ltvs) (EL j vs)
      (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory) ==>
  tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t
Proof
  strip_tac >>
  `tuple_place_snapshot cenv cx ff lo sb.cs_next_id tys ltys ltvs w t` by
    (irule tuple_place_snapshot_endpoint >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> conj_tac
  >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rpt strip_tac >>
  `MEM (EL j elems) elems` by (irule listTheory.EL_MEM >> simp[]) >>
  `?x. EL j elems = Var x` by gvs[listTheory.EVERY_MEM] >>
  `not_fresh_at sp x` by metis_tac[] >>
  `i <= j` by simp[] >>
  qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `j` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  qexists `v` >> simp[]
QED

Theorem tuple_place_pointer_head_advance:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  ci_mono sa sb /\ i < LENGTH ltys /\
  write_place cx p v ee = (INL (),ff) /\
  stmt_state_rel ctx func cenv cx ff t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!j. SUC i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
    val_in_memory (EL j ltvs) (EL j vs)
      (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory) ==>
  tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t
Proof
  strip_tac >>
  `ci_mono sp sa` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >> simp[]) >>
  `sp.cs_next_var <= sa.cs_next_var /\ sp.cs_next_id <= sa.cs_next_id /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM ff.scopes` by
    (drule_all tuplePlaceBorrowTheory.tuple_place_pure_target_scopes >> strip_tac >>
     drule vyperScopePreservationTheory.write_place_scopes_dom >> simp[]) >>
  `!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==>
    lookup_var x t = SOME v` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     fs[loweringPostsTheory.target_post_def]) >>
  `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry` by
    (fs[loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  `!n b sz. local_region cenv ff.scopes t n b sz <=>
    local_region cenv es.scopes s0 n b sz` by
    (irule tuple_place_endpoint_local_regions_some >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  irule tuple_place_head_advance_some >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[]
QED

Theorem tuple_place_equal_storage_head_step:
  tuple_place_head ctx func cenv cx es lo sp tys tys tvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit tys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ ~is_word_type (EL i tys) /\ cenv.ce_target CapMcopy /\
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) src_loc
    (EL i tys) (EL i tys)
    (case EL i tys of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv (EL i tys)) sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys tys tvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuplePlaceBranchReadyTheory.tuple_place_pointer_equal_storage_store >>
  strip_tac >> qexists `t` >> simp[] >>
  `ci_mono sa sb` by
    (metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_stmt_helpers, pairTheory.SND]) >>
  irule tuple_place_pointer_head_advance >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >> simp[] >>
  qexistsl [`tops`, `INL (PlaceR p)`, `bt`] >> simp[] >> rpt strip_tac >>
  `i <= j` by simp[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule tuplePlacePointerReadyTheory.tuple_place_pointer_pending_memory >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

(* Whole snapshot separation is derived from ownership or a typed borrow,
   not imposed on callers of the eventual successful-head step. *)
Theorem tuple_place_pointer_snapshot_apart:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) /\
  write_place cx p (EL i vs) ee = (INL (),ff) ==>
  EVERY is_word_type ltys \/
  w2n w + type_memory_size_list ltvs <= w2n dw \/
  w2n dw + type_memory_size (EL i tvs) <= w2n w
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_pointer_source_facts >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[loweringPostsTheory.target_post_def] >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s` by
    (irule tuplePlacePointerReadyTheory.tuple_place_pointer_snapshot >> metis_tac[]) >>
  `0 < type_memory_size_list ltvs` by
    (drule_all tuplePlaceZeroTheory.tuple_place_element_source_positive >> strip_tac >>
     `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
       <= type_memory_size_list ltvs` by
       (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
        irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >> decide_tac) >>
  fs[tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
  >- (disj2_tac >>
      drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> strip_tac >>
      `b+sz <= b' \/ b'+len <= b` by metis_tac[] >> decide_tac) >>
  `ltvs = tvs` by gvs[] >>
  qpat_x_assum `ltys = tys` SUBST_ALL_TAC >>
  qpat_x_assum `ltvs = tvs` SUBST_ALL_TAC >>
  `writable_place_result cx ee (PlaceR p)` by
    (irule tuplePlacePointerReadyTheory.tuple_place_target_endpoint_writable >>
     fs[targetPlaceSimTheory.target_pre_def] >> metis_tac[]) >>
  `w2n w = b + (w2n w-b)` by simp[] >>
  `w2n w + type_memory_size_list tvs <= w2n dw \/
   w2n dw + type_memory_size (EL i tvs) <= w2n w` suffices_by simp[] >>
  drule_all tuplePlaceReachableTheory.tuple_place_local_path_extent >> strip_tac >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_writable_borrow_destination_apart >>
  simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem tuple_place_pointer_window_transport:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  mem_bytes_at (w2n w) (type_memory_size_list ltvs) t.vs_memory =
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory
Proof
  strip_tac >>
  `val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
    (irule tuplePlacePointerReadyTheory.tuple_place_pointer_pending_memory >>
     metis_tac[]) >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        listTheory.LIST_REL_EL_EQN] >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
    <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s.vs_memory`] >> simp[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  qexists `type_memory_size_list ltvs` >> simp[]
QED

Theorem tuple_place_word_head_step:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\ is_word_type (EL i tys) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
    | _ => MSTORE) [dst; EL i elems] sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (loc = LocMemory ==> w2n w + type_memory_size_list ltvs <= w2n dw \/
    w2n dw + type_memory_size (EL i tvs) <= w2n w) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  drule_all tuplePlaceBranchReadyTheory.tuple_place_pointer_word_store >> strip_tac >>
  qexists `t` >> simp[] >>
  `ci_mono sa sb` by
    (metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND]) >>
  `LENGTH ltys = LENGTH tys` by metis_tac[vyperTypeArgFitsTheory.arg_types_fit_LENGTH] >>
  irule tuple_place_pointer_head_advance >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >> simp[] >>
  qexistsl [`tops`, `INL (PlaceR p)`, `bt`] >> simp[] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule tuple_place_pointer_window_transport >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_SUC_REFL]
QED

Theorem tuple_place_pointer_slice_transport:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target_pure tops bt /\ eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  (w2n w + type_memory_size_list ltvs <= d \/ d+len <= w2n w) /\
  (!name b sz a n. local_region cenv ee.scopes s name b sz /\ b <= a /\
    a+n <= b+sz /\ (a+n <= d \/ d+len <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
  (!aid b sz a n. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= a /\ a+n <= b+sz /\
    (a+n <= d \/ d+len <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) /\
  0 < type_memory_size (EL j ltvs) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s` by
    (irule tuplePlacePointerReadyTheory.tuple_place_pointer_snapshot >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee s /\ LENGTH ltvs = LENGTH ltys` by
    fs[loweringPostsTheory.target_post_def, tuplePlaceHeadTheory.tuple_place_head_def] >>
  `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
    <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >>
  `w2n w + SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
     <= d \/ d+len <= w2n w + SUM (MAP type_memory_size (TAKE j ltvs))` by decide_tac >>
  `mem_bytes_at (w2n w + SUM (MAP type_memory_size (TAKE j ltvs)))
     (type_memory_size (EL j ltvs)) t.vs_memory =
   mem_bytes_at (w2n w + SUM (MAP type_memory_size (TAKE j ltvs)))
     (type_memory_size (EL j ltvs)) s.vs_memory` by
    (drule_all tuplePlacePointerReadyTheory.tuple_place_snapshot_element_bounds >>
     strip_tac >> metis_tac[]) >>
  `val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
    (irule tuplePlacePointerReadyTheory.tuple_place_pointer_pending_memory >> metis_tac[]) >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        listTheory.LIST_REL_EL_EQN] >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >> simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s.vs_memory`] >>
  gvs[]
QED

