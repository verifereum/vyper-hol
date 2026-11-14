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

Theorem tuple_loaded_owned_run[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  cenv.ce_target CapMcopy /\ type_alloc_ok cenv (TupleT tys) /\
  i < LENGTH tys /\ ~is_word_type (EL i ltys) /\
  compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) NONE
    (EL i tys) (EL i ltys)
    (type_memory_bytes cenv (EL i tys)) sa = ((),sb) /\
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
  (loc = LocMemory ==> w2n w + type_memory_size_list ltvs <= w2n dw \/
    w2n dw + type_memory_size (EL i tvs) <= w2n w) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!id lb len a n dtv. id < sa.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (lb,len) /\ lb <= a /\ a+n <= lb+len /\
      evaluate_type (get_tenv cx) (EL i tys) = SOME dtv /\
      (loc = LocMemory ==> a+n <= w2n dw \/ w2n dw+type_memory_size dtv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy` by simp[] >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_sizes >> strip_tac >>
  `i < LENGTH ltys` by simp[] >>
  `evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (drule tuple_loaded_element_value_rel >> simp[]) >>
  `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    w2n sw = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> rpt strip_tac >> gvs[]) >>
  `type_alloc_ok cenv (EL i tys)` by
    (irule tuplePlaceBoundsTheory.tuple_place_element_alloc_ok >> metis_tac[]) >>
  `loc = LocMemory ==> w2n dw + type_memory_size (EL i tvs) < dimword (:256)` by
    (strip_tac >> gvs[] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule tuplePlaceBoundsTheory.tuple_place_memory_end_bound >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >> simp[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  `b+sz <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        exprLoweringPropsTheory.stmt_state_rel_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >>
  `value_has_type (EL i ltvs) (EL i vs) /\
   (!x. EL i elems = Var x ==> not_fresh_at sa x)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[listTheory.EL_MEM]) >>
  irule tuplePlaceOwnedValueFrameTheory.tuple_place_owned_value_run_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> simp[] >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  conj_tac >- (rpt strip_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> decide_tac) >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem tuple_loaded_equal_memory_run[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys tys tvs vs elems w i s /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ ~is_word_type (EL i tys) /\
  0 < type_memory_size (EL i tvs) /\
  type_memory_size (EL i tvs)+64 < dimword (:256) /\
  compile_assign_value cenv dst LocMemory (EL i elems) F NONE
    (EL i tys) (EL i tys) (type_memory_bytes cenv (EL i tys)) sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env ee /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!name b len a n. local_region cenv ee.scopes s name b len /\ b <= a /\
      a+n <= b+len /\ (a+n <= w2n dw \/ w2n dw+type_memory_size (EL i tvs) <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!aid b len a n. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
      (a+n <= w2n dw \/ w2n dw+type_memory_size (EL i tvs) <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  strip_tac >>
  `LENGTH tvs = LENGTH tys` by fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by
    (gvs[vyperValueTheory.evaluate_type_def,
         vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
     drule exprSimAttributeFieldsTheory.opt_mmap_el >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `expr_val_rel cx (EL i tys) (EL i vs) (EL i elems) s` by
    (drule tuple_loaded_element_value_rel >> simp[]) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys tys tvs w s /\
   stmt_state_rel ctx func cenv cx ee s` by fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_snapshot_element_bounds >> strip_tac >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    ?b len. b <= w2n sw /\ w2n sw+type_memory_size (EL i tvs) <= b+len /\
      ((?name. local_region cenv ee.scopes s name b len) \/
       (?aid. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id))` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `i` mp_tac) >> simp[] >>
     strip_tac >> rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule tuplePlaceEqualMemoryTheory.tuple_place_equal_memory_run_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> simp[] >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def,
     vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem tuple_loaded_equal_storage_run[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys tys tvs vs elems w i s /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit tys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ ~is_word_type (EL i tys) /\ cenv.ce_target CapMcopy /\
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) NONE
    (EL i tys) (EL i tys)
    (type_memory_bytes cenv (EL i tys)) sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_memory = s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  drule_all tuplePlaceZeroTheory.tuple_place_element_source_positive >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  `expr_val_rel cx (EL i tys) (EL i vs) (EL i elems) s` by
    (drule tuple_loaded_element_value_rel >> simp[]) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys tys tvs w s /\
   stmt_state_rel ctx func cenv cx ee s` by fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `w2n w + SUM (MAP type_memory_size (TAKE i tvs)) +
     type_memory_size (EL i tvs) <= s.vs_alloca_next` by
    (drule_all tuplePlacePointerReadyTheory.tuple_place_snapshot_element_bounds >> strip_tac
     >- (fs[exprLoweringPropsTheory.stmt_state_rel_def,
             venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     drule_all bodyMemoryDefsTheory.body_local_region_frontier >> decide_tac) >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    w2n sw + type_memory_size (EL i tvs) <= s.vs_alloca_next` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `i` mp_tac) >> simp[] >>
     strip_tac >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `value_has_type (EL i tvs) (EL i vs) /\
   (!x. EL i elems = Var x ==> not_fresh_at sa x) /\
   local_ptrs_reserved cenv sa /\ ~s.vs_halted /\
   s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[listTheory.EL_MEM]) >>
  irule tuplePlaceBorrowStoreTheory.tuple_place_equal_storage_run_memory >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> gvs[]
QED

Theorem tuple_loaded_mutable_store_step:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (if is_word_type (EL i ltys) then
     compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) (SOME loc)
   else compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) NONE
     (EL i tys) (EL i ltys)
     (type_memory_bytes cenv (EL i tys))) sa = ((),sb) /\
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
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_fit >> strip_tac >>
  Q.SUBGOAL_THEN `loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient` assume_tac
  >- (Cases_on `p` >> gvs[loweringPostsTheory.place_ptr_rel_def] >>
      Cases_on `b` >> gvs[loweringPostsTheory.slot_loc_def]) >>
  Cases_on `is_word_type (EL i ltys)`
  >- (Cases_on `loc` >> gvs[stmtLoweringTheory.compile_store_at_loc_def] >>
      irule tuple_loaded_word_store >>
      qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qexistsl [`tvs`, `env`, `dst`] >>
      simp[listTheory.EVERY_NOT_EXISTS, combinTheory.o_DEF]) >>
  `~EVERY is_word_type ltys` by
    (simp[listTheory.EXISTS_MEM] >> qexists `EL i ltys` >>
     simp[] >> irule listTheory.EL_MEM >>
     metis_tac[vyperTypeArgFitsTheory.arg_types_fit_LENGTH]) >>
  `loc = LocMemory ==> w2n w + type_memory_size_list ltvs <= w2n dw \/
    w2n dw + type_memory_size (EL i tvs) <= w2n w` by metis_tac[] >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_sizes >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs)` by metis_tac[] >>
  qsuff_tac `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) t.vs_memory =
      mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory /\
    (!aid off sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      (loc = LocMemory ==> off+sz <= w2n dw \/ w2n dw+type_memory_size (EL i tvs) <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory)`
  >- (strip_tac >> qexists `t` >> simp[] >> conj_tac
      >- (irule tuple_loaded_store_finish >>
          qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
          simp[] >> qexists `p` >> simp[] >> conj_tac
          >- (rpt strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
              irule tuple_loaded_window_transport >>
              qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
              simp[]) >>
          qpat_x_assum `(if _ then _ else _) sa = ((),sb)` mp_tac >>
          simp[] >> strip_tac >>
          metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_stmt_helpers, pairTheory.SND]) >>
      irule tuplePlaceStepTheory.tuple_place_store_alloca_frame >>
      qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
      qexistsl [`func`, `EL i tvs`, `ctx`] >> simp[] >>
      drule vyperScopePreservationTheory.write_place_scopes_dom >>
      disch_then assume_tac >>
      fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
      rpt strip_tac >>
      qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` irule >>
      simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `0 < type_memory_size_list ltvs` by
    (`SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
        <= type_memory_size_list ltvs` by
       (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
        irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >>
     decide_tac) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s` by
    fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  qpat_x_assum `tuple_place_snapshot _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[tuplePlacePrefixCertTheory.tuple_place_snapshot_def] >>
  disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
  >- metis_tac[] >>
  disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
  >- gvs[] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `aid` (qx_choose_then `b` (qx_choose_then `sz`
      (map_every assume_tac o CONJUNCTS)))) mp_tac)
  >- (qpat_x_assum `(if _ then _ else _) sa = ((),sb)` mp_tac >>
      simp[] >> disch_tac >>
      `w2n w + type_memory_size_list ltvs <= b+sz` by decide_tac >>
      drule_all tuple_loaded_owned_run >>
      strip_tac >> qexists `t` >> simp[] >>
      conj_tac
      >- (qpat_x_assum `!id lb len a n dtv. _ ==> _` irule >>
          metis_tac[]) >>
      rpt strip_tac >> qpat_x_assum `!id lb len a n dtv. _ ==> _` irule >>
      conj_tac >- (qexistsl [`aid'`, `off`, `sz'`] >> simp[]) >>
      qexists `EL i tvs` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  disch_then (qx_choose_then `n` (qx_choose_then `b` (qx_choose_then `sz`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_x_assum `ltys = tys` SUBST_ALL_TAC >>
  (Cases_on `loc = LocMemory`
  >- (gnvs[] >>
      `type_memory_size (EL i ltvs)+64 < dimword (:256)` by metis_tac[] >>
      drule_all tuple_loaded_equal_memory_run >> strip_tac >>
      qexists `t` >> simp[] >> conj_tac
      >- (qpat_x_assum `!name b len a n. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
          conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
          qexistsl [`b`, `sz`, `n`] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      rpt strip_tac >>
      (qpat_x_assum `!aid b len a n. _ ==> _` irule >>
       conj_tac
       >- (qexistsl [`aid`, `off`, `sz'`] >> simp[]) >>
       decide_tac)) >>
  gnvs[] >>
  `loc = LocStorage \/ loc = LocTransient` by metis_tac[] >>
  drule tuple_loaded_equal_storage_run >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists `t` >> simp[])
QED
