(* Store-side owned tuple certificates, independent of target evaluation. *)
Theory tupleAssignEffectfulIndexOwnedStore
Ancestors
  tuplePlaceStep tuplePlaceHead tuplePlaceHeadAdvance tuplePlaceOwnedValueFrame
  tuplePlaceFramedStore tuplePlacePointerReady tuplePlaceSource tuplePlaceBounds
  stmtSimDefs loweringPosts list

Theorem tuple_effectful_owned_store_advance[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sa.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) /\
  i < LENGTH ltys /\ ci_mono sa sb /\
  MAP FDOM ee.scopes = MAP FDOM ff.scopes /\
  stmt_state_rel ctx func cenv cx ff t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  alloca_frame cenv ee sa s cenv ff t ==>
  tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
      aid < sb.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv ff.scopes t n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n b sz. local_region cenv ff.scopes t n b sz <=>
             local_region cenv ee.scopes s n b sz` by
    (irule tuple_place_endpoint_local_regions_some >> fs[tuple_place_head_def] >>
     metis_tac[]) >>
  conj_tac
  >- (irule tuple_place_head_advance >>
      qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
        fs[exprLoweringPropsTheory.ci_mono_def] >>
      simp[] >> rpt strip_tac >>
      `val_in_memory (EL j ltvs) (EL j vs)
        (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
        fs[tuple_place_head_def] >>
      `val_wf (EL j ltvs) (EL j vs)` by
        (fs[tuple_place_head_def, vyperTypeDefaultsTheory.values_have_types_LIST_REL,
            LIST_REL_EL_EQN] >>
         metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
      `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
        <= type_memory_size_list ltvs` by
        (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
         irule tupleMemoryLayoutTheory.tuple_element_interval >> fs[tuple_place_head_def]) >>
      `mem_bytes_at (w2n w) (type_memory_size_list ltvs) t.vs_memory =
        mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory` by
        (qpat_x_assum `EVERY _ _ \/ _` strip_assume_tac
         >- gvs[EVERY_EL]
         >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
         fs[alloca_frame_def] >>
         `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by metis_tac[] >>
         drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`w2n w-b`,`type_memory_size_list ltvs`] mp_tac) >> simp[]) >>
      irule valueEncodingPropsTheory.val_in_memory_mem_agree >> conj_tac >- simp[] >>
      qexistsl [`type_memory_size (EL j ltvs)`,`s.vs_memory`] >> simp[] >>
      drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
      disch_then (qspecl_then
        [`SUM (MAP type_memory_size (TAKE j ltvs))`,`type_memory_size (EL j ltvs)`]
        mp_tac) >> gvs[]) >>
  qpat_x_assum `EVERY _ _ \/ _` strip_assume_tac >> simp[] >>
  disj2_tac >> disj2_tac >> qexistsl [`aid`,`b`,`sz`] >>
  fs[exprLoweringPropsTheory.ci_mono_def, alloca_frame_def] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem tuple_effectful_current_value_rel[local]:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
  i < LENGTH ltys ==>
  expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s
Proof
  strip_tac >>
  `?v. eval_operand (EL i elems) s = SOME v /\
    if is_word_type (EL i ltys) then v = typed_val_to_w256 (EL i ltvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    fs[tuple_place_head_def] >>
  simp[expr_val_rel_def] >> Cases_on `is_word_type (EL i ltys)` >- gvs[] >>
  gvs[] >> fs[tuple_place_head_def]
QED

Theorem tuple_effectful_owned_store_head:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sa.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (if is_word_type (EL i ltys) then
    emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
      [dst; EL i elems]
   else compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) src_loc
    (EL i tys) (EL i ltys)
    (case EL i tys of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv (EL i tys))) sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
      ?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
        aid < sb.cs_next_id /\ b <= w2n w /\
        w2n w + type_memory_size_list ltvs <= b+sz /\
        (!n lb lsz. local_region cenv ff.scopes t n lb lsz ==>
          b+sz <= lb \/ lb+lsz <= b)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) (EL i tys) /\
   0 < type_slot_size (EL i tvs)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  `i < LENGTH ltys` by simp[] >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (irule tuple_effectful_current_value_rel >> metis_tac[]) >>
  `value_has_type (EL i ltvs) (EL i vs) /\
   (!x. EL i elems = Var x ==> not_fresh_at sa x) /\
   stmt_state_rel ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
   ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts` by
    (fs[tuple_place_head_def, vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        LIST_REL_EL_EQN] >> metis_tac[EL_MEM]) >>
  Cases_on `is_word_type (EL i ltys)`
  >- suspend "word"
  >> suspend "owned"
QED

Resume tuple_effectful_owned_store_head[word]:
  drule_all tuple_place_index_fit >> strip_tac >>
  `is_word_type (EL i tys)` by gvs[] >>
  `EL i ltys = EL i tys` by
    (drule_all typedMemoryCopyTheory.typed_copy_word_widening >> simp[]) >>
  `is_word_type (EL i tys) /\ EL i ltvs = EL i tvs /\
   value_has_type (EL i tvs) (EL i vs)` by gvs[] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!off sz. (loc = LocMemory ==> off+sz <= w2n dw \/
      w2n dw+type_memory_size (EL i tvs) <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory)` by
    (qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >> simp[] >> disch_tac >>
     `expr_val_rel cx (EL i tys) (EL i vs) (EL i elems) s` by metis_tac[] >>
     `loc = LocMemory ==> 0+0 <= w2n dw \/
        w2n dw+type_memory_size (EL i tvs) <= 0` by simp[] >>
     drule_all (tuple_place_word_run_frame |> SPEC_ALL |>
       Q.INST [`a` |-> `0`, `n` |-> `0`]) >>
     disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists `t` >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ci_mono sa sb` by
    (gvs[] >> metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND]) >>
  `alloca_frame cenv ee sa s cenv ff t` by
    (irule tuple_place_store_alloca_frame >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >> simp[] >>
     qexistsl [`func`,`ctx`] >> simp[] >>
     metis_tac[vyperScopePreservationTheory.write_place_scopes_dom,
       arithmeticTheory.ADD_COMM]) >>
  `MAP FDOM ee.scopes = MAP FDOM ff.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  drule_all tuple_effectful_owned_store_advance >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists `t` >> simp[]
QED

Resume tuple_effectful_owned_store_head[owned]:
  drule_all tuple_place_index_sizes >> strip_tac >>
  `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >>
  qpat_x_assum `EVERY _ _ \/ _` strip_assume_tac
  >- gvs[EVERY_EL]
  >- gvs[] >>
  `w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
    type_memory_size (EL i ltvs) < dimword (:256)` by
    (`b+sz <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)` by
      (fs[exprLoweringPropsTheory.stmt_state_rel_def,
          venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
       metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >> decide_tac) >>
  `!sw. eval_operand (EL i elems) s = SOME sw ==>
    w2n sw = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))` by
    (fs[tuple_place_head_def] >>
     qpat_x_assum `!j. i <= j /\ j < LENGTH tys ==> ?v. _`
       (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> rpt strip_tac >> gvs[]) >>
  `loc = LocMemory ==> w2n dw + type_memory_size (EL i tvs) < dimword (:256) /\
    (w2n w + SUM (MAP type_memory_size (TAKE i ltvs)) +
       type_memory_size (EL i ltvs) <= w2n dw \/
     w2n dw + type_memory_size (EL i tvs) <=
       w2n w + SUM (MAP type_memory_size (TAKE i ltvs)))` by
    (strip_tac >> gvs[] >>
     `w2n dw + type_memory_size (EL i tvs) < dimword (:256)` by
       (drule_all tuple_place_memory_end_bound >> simp[]) >>
     drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> strip_tac >>
     `b+sz <= b' \/ b'+len <= b` by metis_tac[] >> decide_tac) >>
  `type_alloc_ok cenv (EL i tys)` by
    (irule tuple_place_element_alloc_ok >> metis_tac[]) >>
  qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >> simp[] >> disch_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!id lb len a n dtv. id < sa.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (lb,len) /\ lb <= a /\ a+n <= lb+len /\
      evaluate_type (get_tenv cx) (EL i tys) = SOME dtv /\
      (loc = LocMemory ==> a+n <= w2n dw \/ w2n dw+type_memory_size dtv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)` by
    (irule tuple_place_owned_value_run_frame >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
     simp[] >> qexists `EL i vs` >> simp[] >> conj_tac
     >- metis_tac[arithmeticTheory.ADD_COMM] >> conj_tac
     >- (rpt strip_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> decide_tac) >>
     rpt strip_tac >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `ci_mono sa sb` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_stmt_helpers, pairTheory.SND]) >>
  `MAP FDOM ee.scopes = MAP FDOM ff.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  `alloca_frame cenv ee sa s cenv ff t` by
    (irule tuple_place_store_alloca_frame >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >> simp[] >>
     qexistsl [`func`,`ctx`] >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!id lb len a n dtv. _` irule >>
     conj_tac
     >- (qexistsl [`aid'`,`off`,`sz'`] >> simp[]) >>
     qexists `EL i tvs` >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  Q.SUBGOAL_THEN
   `EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sa.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)` assume_tac >-
    (disj2_tac >> disj2_tac >> qexistsl [`aid`,`b`,`sz`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!n lb lsz. local_region _ _ _ _ _ _ ==> _` drule >> simp[]) >>
  drule_all tuple_effectful_owned_store_advance >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists `t` >> conj_tac
  >- (qpat_assum `gas_marked_path _ _ _ _ _ _` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ (SUC _) _` ACCEPT_TAC) >>
  conj_tac >-
    (qpat_x_assum `EVERY _ _ \/ _ \/ ?aid b sz. FLOOKUP t.vs_allocas _ = _ /\ _`
       strip_assume_tac
     >- simp[]
     >- (gvs[] >> decide_tac) >>
     disj2_tac >> qexistsl [`aid'`,`b'`,`sz'`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!n lb lsz. local_region _ _ _ _ _ _ ==> _` drule >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Finalise tuple_effectful_owned_store_head
