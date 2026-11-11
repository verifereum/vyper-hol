(* Loaded mutable stores use the successful pointer endpoint, not purity. *)
Theory tupleAssignImmutableDeployLoadedStore
Ancestors
  tuplePlaceStep tuplePlaceOwnedValueFrame tuplePlaceEqualMemory
  tuplePlaceBorrowStore tuplePlaceFramedStore

Theorem tuple_loaded_element_value_rel[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
  i < LENGTH ltys ==>
  expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s
Proof
  strip_tac >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  simp[loweringPostsTheory.expr_val_rel_def] >>
  Cases_on `is_word_type (EL i ltys)` >> gvs[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[]
QED

(* A store's byte frame is consumed at its correctness endpoint. *)
Theorem tuple_loaded_store_finish[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  i < LENGTH ltys /\ ci_mono sa sb /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
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
  `MAP FDOM ee.scopes = MAP FDOM ff.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  `!n b sz. local_region cenv ff.scopes t n b sz <=>
    local_region cenv ee.scopes s n b sz` by
    (irule tuplePlaceHeadAdvanceTheory.tuple_place_endpoint_local_regions >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  irule tuplePlaceHeadAdvanceTheory.tuple_place_head_advance >>
  goal_assum (drule_at Any) >>
  fs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[]
QED

Theorem tuple_loaded_window_transport[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  mem_bytes_at (w2n w) (type_memory_size_list ltvs) t.vs_memory =
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory
Proof
  strip_tac >>
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
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >> simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s.vs_memory`] >>
  conj_tac >- fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then
    [`SUM (MAP type_memory_size (TAKE j ltvs))`, `type_memory_size (EL j ltvs)`]
    mp_tac) >> simp[] >>
  gvs[tuplePlaceHeadTheory.tuple_place_head_def]
QED

Theorem tuple_loaded_word_store[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\ is_word_type (EL i tys) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
    | _ => MSTORE) [dst; EL i elems] sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (loc = LocMemory /\ ~EVERY is_word_type ltys ==>
    w2n w + type_memory_size_list ltvs <= w2n dw \/
    w2n dw + type_memory_size (EL i tvs) <= w2n w) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_fit >> strip_tac >>
  `i < LENGTH ltys` by metis_tac[] >>
  `EL i ltys = EL i tys` by
    metis_tac[typedMemoryCopyTheory.typed_copy_word_widening] >>
  `evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (drule tuple_loaded_element_value_rel >> simp[]) >>
  `expr_val_rel cx (EL i tys) (EL i vs) (EL i elems) s` by metis_tac[] >>
  `EL i ltvs = EL i tvs` by metis_tac[optionTheory.SOME_11] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        listTheory.LIST_REL_EL_EQN] >>
     qpat_x_assum `!n. n < _ ==> value_has_type _ _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_bytes_at 0 0 t.vs_memory = mem_bytes_at 0 0 s.vs_memory /\
    (!off sz. (loc = LocMemory ==>
      off+sz <= w2n dw \/ w2n dw+type_memory_size (EL i tvs) <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory)` by
    (irule tuplePlaceFramedStoreTheory.tuple_place_word_run_frame >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >> simp[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  qexists `t` >> simp[] >> conj_tac
  >- (irule tuple_loaded_store_finish >>
      qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >>
      `ci_mono sa sb` by
        metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
      simp[] >> qexists `p` >> simp[] >> rpt strip_tac >>
      `~EVERY is_word_type ltys` by
        (simp[listTheory.EXISTS_MEM] >> qexists `EL j ltys` >>
         simp[] >> metis_tac[listTheory.EL_MEM]) >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule tuple_loaded_window_transport >>
      qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> gvs[]) >>
  irule tuplePlaceStepTheory.tuple_place_store_alloca_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qexistsl [`func`, `EL i tvs`, `ctx`] >> simp[] >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  metis_tac[vyperScopePreservationTheory.write_place_scopes_dom]
QED
