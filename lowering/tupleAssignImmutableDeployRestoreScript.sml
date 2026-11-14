(* Endpoint restoration for a loaded immutable element. Normalization is
   identity for equal layouts, in particular for borrowed snapshots. *)
Theory tupleAssignImmutableDeployRestore
Ancestors
  tuplePlaceHeadAdvance immutableAssignCompose tuplePlacePointerReady
  externalReturnBufferlessNormalize

Theorem tuple_immutable_pending_memory[local]:
  tuple_place_head ctx func ce cx es lo sa tys ltys ltvs vs elems w i s /\
  ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  (ltys = tys ==> r = s) /\
  (!a k. regions_disjoint a k off (type_memory_size itv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
  (!aid b len a k. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
    aid < sa.cs_next_id /\ b <= a /\ a+k <= b+len /\
    (!name lb sz. local_region ce es.scopes s name lb sz ==>
      b+len <= lb \/ lb+sz <= b) /\
    regions_disjoint a k off (type_memory_size itv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) q.vs_memory
Proof
  strip_tac >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  Cases_on `type_memory_size (EL j ltvs) = 0`
  >- metis_tac[return_zero_wf_memory] >>
  `stmt_state_rel ctx func ce cx es s /\ LENGTH ltvs = LENGTH ltys /\
   tuple_place_snapshot ce cx es lo sa.cs_next_id tys ltys ltvs w s /\
   val_in_memory (EL j ltvs) (EL j vs)
     (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
    fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_declared_region >> strip_tac >>
  `0 < type_memory_size (EL j ltvs)` by simp[] >>
  drule_all tuple_place_snapshot_element_bounds >> strip_tac
  >- (`regions_disjoint
        (w2n w + SUM (MAP type_memory_size (TAKE j ltvs)))
        (type_memory_size (EL j ltvs)) off (type_memory_size itv)` by
        (qpat_x_assum `!aid b sz. FLOOKUP _ _ = _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >> decide_tac) >>
      irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
      conj_tac >- simp[] >>
      qexistsl [`type_memory_size (EL j ltvs)`, `s.vs_memory`] >>
      pure_asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >> metis_tac[]) >>
  `r = s` by simp[] >>
  `regions_disjoint
     (w2n w + SUM (MAP type_memory_size (TAKE j ltvs)))
     (type_memory_size (EL j ltvs)) off (type_memory_size itv)` by
    (qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >> decide_tac) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s.vs_memory`] >>
  pure_asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >> metis_tac[]
QED

Theorem tuple_immutable_endpoint_restore:
  tuple_place_head ctx func ce cx es lo sa tys ltys ltvs vs elems w i s /\
  i < LENGTH ltys /\ ci_mono sa sb /\ expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es r /\ alloca_frame ce es sa s ce es r /\
  (ltys = tys ==> r = s) /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  write_place cx (ImmutablePlace ce.ce_module id []) (EL i vs) es = (INL (),ff) /\
  immutable_value_admissible itv (EL i vs) /\
  val_in_memory itv (EL i vs) off q.vs_memory /\
  immutable_value_bytes_rel itv (EL i vs)
    (mem_bytes_at off (type_memory_size itv) q.vs_memory) /\
  (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
    vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
  (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x r) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP r.vs_allocas aid = SOME entry) /\
  (!aid entry. FLOOKUP r.vs_allocas aid = SOME entry ==>
    FLOOKUP q.vs_allocas aid = SOME entry) /\
  LENGTH r.vs_memory <= LENGTH q.vs_memory /\
  (!a k. regions_disjoint a k off (type_memory_size itv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
  (!aid b len a k. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
    aid < sa.cs_next_id /\ b <= a /\ a+k <= b+len /\
    (!name lb sz. local_region ce es.scopes s name lb sz ==>
      b+len <= lb \/ lb+sz <= b) /\
    regions_disjoint a k off (type_memory_size itv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
  q.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  tuple_place_head ctx func ce cx ff lo sb tys ltys ltvs vs elems w (SUC i) q /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP q.vs_allocas aid = SOME entry) /\
  alloca_frame ce es sa s ce ff q
Proof
  strip_tac >>
  `local_ptrs_reserved ce sa` by fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `expr_sim_inv ce cx env es` by simp[] >>
  `stmt_state_rel ctx func ce cx ff q` by
    (irule immutableDeployAssignRestoreTheory.immutable_store_stmt_state_rel >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
     qpat_assum `evaluate_type _ _ = _` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved _ _` (irule_at Any) >>
     qexists `r` >> simp[]) >>
  `ff.scopes = es.scopes` by
    metis_tac[vyperPlaceFramesTheory.write_immutable_place_scopes] >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by metis_tac[] >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP q.vs_allocas aid = SOME entry` by metis_tac[] >>
  `alloca_frame ce es sa r ce ff q` by
    (irule immutable_assign_suffix_alloca_frame >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `alloca_frame ce es sa s ce ff q` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl [`ce`, `es`, `r`, `sa`] >> simp[]) >>
  simp[] >> irule tuple_place_head_advance >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule tuple_immutable_pending_memory >>
      qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexistsl [`r`, `off`, `ity`, `itv`, `id`] >> simp[] >> gvs[]) >>
  conj_tac
  >- (irule tuple_place_endpoint_local_regions >>
      simp[] >> qexists `sa` >> simp[]) >>
  fs[exprLoweringPropsTheory.ci_mono_def]
QED
