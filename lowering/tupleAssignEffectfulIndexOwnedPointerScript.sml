(* Owned tuple heads survive arbitrary effectful target evaluation. *)
Theory tupleAssignEffectfulIndexOwnedPointer
Ancestors
  tuplePlacePointerReady tuplePlaceStep tuplePlaceHead tuplePlaceSnapshot
  list vyperEvalExprPreservesScopesDom

Theorem tuple_effectful_owned_pending_memory[local]:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      aid < sp.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s0.vs_memory` by
    fs[tuple_place_head_def] >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (fs[tuple_place_head_def, vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        LIST_REL_EL_EQN] >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
    <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >> fs[tuple_place_head_def]) >>
  `mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory =
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) s0.vs_memory` by
    (qpat_x_assum `EVERY _ _ \/ _` strip_assume_tac
     >- gvs[EVERY_EL]
     >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
     drule_all tuple_place_target_allocation >> strip_tac >>
     drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`w2n w-b`, `type_memory_size_list ltvs`] mp_tac) >>
     simp[]) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s0.vs_memory`] >> simp[] >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then
    [`SUM (MAP type_memory_size (TAKE j ltvs))`, `type_memory_size (EL j ltvs)`]
    mp_tac) >> simp[]
QED

Theorem tuple_effectful_owned_pointer_head:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      aid < sp.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sa.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) /\
  (!n b sz. local_region cenv ee.scopes s n b sz <=>
             local_region cenv es.scopes s0 n b sz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sp sa` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >> simp[]) >>
  `sp.cs_next_id <= sa.cs_next_id /\ sp.cs_next_var <= sa.cs_next_var` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!n b sz. local_region cenv ee.scopes s n b sz <=>
             local_region cenv es.scopes s0 n b sz` by
    (irule tuple_place_endpoint_local_regions_some >>
     fs[tuple_place_head_def, loweringPostsTheory.target_post_def] >>
     metis_tac[eval_base_place_preserves_scopes_dom]) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s` by
    (irule tuplePlaceHeadAdvanceTheory.tuple_place_snapshot_endpoint >>
     fs[tuple_place_head_def, loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (`local_ptrs_reserved cenv sa` by
        (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists `sp` >> fs[tuple_place_head_def]) >>
      `!j. i <= j /\ j < LENGTH ltys ==> ?v.
        eval_operand (EL j elems) s = SOME v /\
        if is_word_type (EL j ltys) then
          v = typed_val_to_w256 (EL j ltvs) (EL j vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))` by
        (rpt strip_tac >> irule tuple_place_head_pointer_operands >> metis_tac[]) >>
      `!j. i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
        val_in_memory (EL j ltvs) (EL j vs)
          (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
        (rpt strip_tac >> irule tuple_effectful_owned_pending_memory >> metis_tac[]) >>
      qpat_x_assum `EVERY _ _ \/ _` kall_tac >>
      fs[tuple_place_head_def, loweringPostsTheory.target_post_def] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_x_assum `EVERY _ _ \/ _` strip_assume_tac >> simp[] >>
  disj2_tac >> disj2_tac >> qexistsl [`aid`,`b`,`sz`] >> simp[] >>
  fs[loweringPostsTheory.target_post_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
