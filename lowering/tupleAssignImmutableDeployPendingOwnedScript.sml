(* Transport of protected pending tuple fields at the actual target endpoint.
   Store execution/restoration is supplied by the existing loaded-store heads. *)
Theory tupleAssignImmutableDeployPendingOwned
Ancestors
  tupleAssignImmutableDeploySnapshot tupleAssignImmutableDeployEffectful
  tupleAssignImmutableDeployRestore placeMemoryLiveRegion
  externalReturnBufferlessNormalize

Theorem tuple_immutable_owned_pending_target[local]:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sp.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))) /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory
Proof
  strip_tac
  >- gvs[listTheory.EVERY_EL]
  >- (`val_wf (EL j ltvs) (EL j vs)` by
        (fs[tuplePlaceHeadTheory.tuple_place_head_def,
            vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
         metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
      `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
         <= type_memory_size_list ltvs` by
        (pure_rewrite_tac[valueEncodingProofsTheory.type_memory_size_list_sum] >>
         irule tupleMemoryLayoutTheory.tuple_element_interval >>
         fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
      `type_memory_size (EL j ltvs) = 0` by decide_tac >>
      metis_tac[return_zero_wf_memory]) >>
  irule tuple_immutable_owned_target_pending >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem tuple_immutable_owned_target_head:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  sp.cs_next_id <= sa.cs_next_id /\ sp.cs_next_var <= sa.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sp.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))) ==>
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sa.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))` by
    (irule tuple_immutable_owned_target_snapshot >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s` by
    (simp[tuplePlacePrefixCertTheory.tuple_place_snapshot_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!j. i <= j /\ j < LENGTH ltys ==>
     ?v. eval_operand (EL j elems) s = SOME v /\
       if is_word_type (EL j ltys) then v = typed_val_to_w256 (EL j ltvs) (EL j vs)
       else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))` by
    (rpt strip_tac >> irule tuplePlacePointerReadyTheory.tuple_place_head_pointer_operands >>
     qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `!j. i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
     val_in_memory (EL j ltvs) (EL j vs)
       (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
    (rpt strip_tac >> irule tuple_immutable_owned_pending_target >>
     qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `local_ptrs_reserved cenv sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> metis_tac[]) >>
  fs[loweringPostsTheory.target_post_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

(* Unlike arbitrary memory pointers, writable target pointers are contained
   in live locals. The full owner's nonlocal separation therefore suffices. *)
Theorem tuple_immutable_owned_destination_apart[local]:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  runtime_place_writable cx ee p /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) ==>
  w2n w + type_memory_size_list ltvs <= w2n dw \/
  w2n dw + type_memory_size dtv <= w2n w
Proof
  rpt strip_tac >> Cases_on `p` >>
  gvs[loweringPostsTheory.place_ptr_rel_def, loweringPostsTheory.slot_loc_def,
      vyperPlaceWriteSoundnessTheory.runtime_place_writable_def, AllCaseEqs()] >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace s' l)) (b' + n2w k)
     (SOME LocMemory) (Type dty)` by
    (simp[loweringPostsTheory.place_ptr_rel_def] >> metis_tac[]) >>
  drule_all tuplePlaceReachableTheory.tuple_place_memory_coordinates >> strip_tac >>
  gvs[] >>
  qpat_x_assum `!n lb lsz. local_region _ _ _ _ _ _ ==> _` drule >>
  strip_tac >> decide_tac
QED

(* Both the mutable loaded head and immutable endpoint restoration return
   alloca_frame at their chosen execution endpoint. It protects the entire
   owner, independently of the storage class of the preceding write. *)
Theorem tuple_immutable_owned_store_certificate:
  alloca_frame cenv es sa s cenv ff t /\ sa.cs_next_id <= sb.cs_next_id /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sa.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))) ==>
  EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sb.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv ff.scopes t n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))
Proof
  strip_tac >> simp[] >> disj2_tac >> disj2_tac >>
  qexistsl [`aid`, `b`, `sz`] >> simp[] >>
  fs[stmtSimDefsTheory.alloca_frame_def] >>
  first_x_assum (qspecl_then [`aid`, `b`, `sz`] mp_tac) >> simp[] >>
  impl_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem tuple_immutable_owned_store_pending:
  tuple_place_head ctx func cenv cx es lo sa tys ltys ltvs vs elems w i s /\
  alloca_frame cenv es sa s cenv ff t /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) /\
  SUC i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory
Proof
  strip_tac >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tupleMemoryLayoutTheory.tuple_element_interval >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[stmtSimDefsTheory.alloca_frame_def] >> metis_tac[]) >>
  `val_in_memory (EL j ltvs) (EL j vs)
     (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory` by
    (`i <= j` by decide_tac >> fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s.vs_memory`] >>
  simp[] >> sym_tac >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then
    [`w2n w + SUM (MAP type_memory_size (TAKE j ltvs)) - b`,
     `type_memory_size (EL j ltvs)`] mp_tac) >> simp[]
QED

Theorem tuple_immutable_owned_head_destination:
  tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
  expr_sim_inv cenv cx env ee /\ runtime_place_writable cx ee p /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\ ~EVERY is_word_type ltys /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sa.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))) ==>
  w2n w + type_memory_size_list ltvs <= w2n dw \/
  w2n dw + type_memory_size (EL i tvs) <= w2n w
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac
  >- (drule_all tuplePlaceZeroTheory.tuple_place_element_source_positive >> strip_tac >>
      `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
         <= type_memory_size_list ltvs` by
        (pure_rewrite_tac[valueEncodingProofsTheory.type_memory_size_list_sum] >>
         irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >>
      decide_tac) >>
  irule tuple_immutable_owned_destination_apart >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qexistsl [`sz`, `func`, `ctx`, `b`] >> simp[] >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]
QED
