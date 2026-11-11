(* Tuple-indexed applications of the same-endpoint store runners. *)
Theory tuplePlaceBranchReady
Ancestors
  tuplePlacePointerReady tuplePlaceFramedStore tuplePlaceOwnedValueFrame
  tuplePlaceEqualMemory tuplePlaceBorrowStore

Theorem tuple_place_pointer_word_store:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
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
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) t.vs_memory =
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory /\
    (!off sz. (loc = LocMemory ==>
      off+sz <= w2n dw \/ w2n dw+type_memory_size (EL i tvs) <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory)
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) (EL i tys)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  drule_all tuple_place_index_fit >> strip_tac >>
  drule_all tuple_place_pointer_source_facts >> strip_tac >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (irule tuple_place_pointer_value_rel >>
     metis_tac[]) >>
  `EL i ltys = EL i tys` by
    metis_tac[typedMemoryCopyTheory.typed_copy_word_widening] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (`EL i ltvs = EL i tvs` by gvs[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        listTheory.LIST_REL_EL_EQN] >>
     qpat_x_assum `!n. _ ==> value_has_type _ _` (qspec_then `i` mp_tac) >> simp[]) >>
  irule tuple_place_word_run_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem tuple_place_pointer_equal_memory_store:
  tuple_place_head ctx func cenv cx es lo sp tys tys tvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ ~is_word_type (EL i tys) /\
  0 < type_memory_size (EL i tvs) /\
  type_memory_size (EL i tvs)+64 < dimword (:256) /\
  compile_assign_value cenv dst LocMemory (EL i elems) F src_loc
    (EL i tys) (EL i tys) arr (type_memory_bytes cenv (EL i tys)) sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
  `LENGTH tvs = LENGTH tys` by
    fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by
    (gvs[vyperValueTheory.evaluate_type_def,
         vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
     drule exprSimAttributeFieldsTheory.opt_mmap_el >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  drule_all tuple_place_pointer_element_facts >> strip_tac >>
  drule_all tuple_place_pointer_source_facts >> strip_tac >>
  `expr_val_rel cx (EL i tys) (EL i vs) (EL i elems) s` by
    (irule tuple_place_pointer_value_rel >> metis_tac[]) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys tys tvs w s` by
    (irule tuple_place_pointer_snapshot >> metis_tac[]) >>
  drule_all tuple_place_snapshot_element_bounds >> strip_tac >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    ?b len. b <= w2n sw /\ w2n sw+type_memory_size (EL i tvs) <= b+len /\
      ((?name. local_region cenv ee.scopes s name b len) \/
       (?aid. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id))` by
    (rpt strip_tac >>
     `?v. eval_operand (EL i elems) s = SOME v /\
       w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
       (`i <= i` by simp[] >>
        drule_all tuple_place_head_pointer_operands >> simp[]) >>
     gvs[] >> metis_tac[]) >>
  irule tuple_place_equal_memory_run_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> gvs[]
QED

Theorem tuple_place_pointer_equal_storage_store:
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
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_memory = s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   type_widens_to (get_tenv cx) (EL i tys) (EL i tys) /\
   0 < type_slot_size (EL i tvs)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  drule_all tuplePlaceZeroTheory.tuple_place_element_source_positive >> strip_tac >>
  drule_all tuple_place_pointer_element_facts >> strip_tac >>
  drule_all tuple_place_pointer_source_facts >> strip_tac >>
  `expr_val_rel cx (EL i tys) (EL i vs) (EL i elems) s` by
    (irule tuple_place_pointer_value_rel >> metis_tac[]) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys tys tvs w s` by
    (irule tuple_place_pointer_snapshot >> metis_tac[]) >>
  `w2n w + SUM (MAP type_memory_size (TAKE i tvs)) +
     type_memory_size (EL i tvs) <= s.vs_alloca_next` by
    (drule_all tuple_place_snapshot_element_bounds >> strip_tac
     >- (fs[exprLoweringPropsTheory.stmt_state_rel_def,
             venomMemDefsTheory.alloca_inv_def,
             venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     `b+sz <= s.vs_alloca_next` by
       (irule bodyMemoryDefsTheory.body_local_region_frontier >>
        goal_assum (drule_at Any) >> metis_tac[]) >> decide_tac) >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    w2n sw + type_memory_size (EL i tvs) <= s.vs_alloca_next` by
    (rpt strip_tac >> `i <= i` by simp[] >>
     drule_all tuple_place_head_pointer_operands >> simp[] >> metis_tac[]) >>
  Cases_on `?et n. EL i tys = ArrayT et (Dynamic n)`
  >- (irule tuple_place_equal_dyn_run_memory >>
      qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
      simp[] >> qexists `EL i vs` >> gvs[]) >>
  irule tuple_place_equal_storage_run_memory >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> gvs[]
QED

Theorem tuple_place_pointer_owned_store:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sp.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\ ~is_word_type (EL i ltys) /\
  compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) src_loc
    (EL i tys) (EL i ltys)
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) (EL i tys) /\
   0 < type_slot_size (EL i tvs)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  drule_all tuple_place_index_sizes >> strip_tac >>
  `i < LENGTH ltys` by simp[] >>
  drule_all tuple_place_pointer_element_facts >> strip_tac >>
  drule_all tuple_place_pointer_source_facts >> strip_tac >>
  drule_all tuple_place_pointer_owned_region >> strip_tac >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (irule tuple_place_pointer_value_rel >> metis_tac[]) >>
  `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >>
  `w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
    type_memory_size (EL i ltvs) < dimword (:256)` by
    (`b+sz <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)` by
      (fs[exprLoweringPropsTheory.stmt_state_rel_def,
          venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
       metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >> decide_tac) >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    w2n sw = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    (rpt strip_tac >> `i <= i` by simp[] >>
     drule_all tuple_place_head_pointer_operands >> simp[] >> metis_tac[]) >>
  `loc = LocMemory ==> w2n dw + type_memory_size (EL i tvs) < dimword (:256) /\
    (w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
       type_memory_size (EL i ltvs) <= w2n dw \/
     w2n dw + type_memory_size (EL i tvs) <=
       w2n w + SUM (MAP type_memory_size (TAKE i ltvs)))` by
    (strip_tac >> gvs[] >>
     `w2n dw + type_memory_size (EL i tvs) < dimword (:256)` by
       (drule_all tuplePlaceBoundsTheory.tuple_place_memory_end_bound >> simp[]) >>
     drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> strip_tac >>
     `b+sz <= b' \/ b'+len <= b` by metis_tac[] >> decide_tac) >>
  `type_alloc_ok cenv (EL i tys)` by
    (irule tuplePlaceBoundsTheory.tuple_place_element_alloc_ok >> metis_tac[]) >>
  irule tuple_place_owned_value_run_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> simp[] >> conj_tac
  >- metis_tac[arithmeticTheory.ADD_COMM] >> conj_tac
  >- (rpt strip_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> decide_tac) >>
  rpt strip_tac >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED
