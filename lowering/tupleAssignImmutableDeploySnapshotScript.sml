(* Protected tuple snapshots do not require purity of target indices.
   The source target transition is retained to obtain scope-domain stability. *)
Theory tupleAssignImmutableDeploySnapshot
Ancestors
  tuplePlacePointerReady tuplePlaceSnapshot tuplePlacePrefixCert tuplePlaceHead
  loweringPosts bodySimAugPlaceStore tupleMemoryLayout
  vyperEvalExprPreservesScopesDom wordArgsPtr

Theorem tuple_immutable_owned_target_snapshot:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sp /\
  eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  sp.cs_next_id <= sa.cs_next_id /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sp.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))) ==>
  EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
   (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     lo <= aid /\ aid < sa.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size_list ltvs <= b+sz /\
     (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b))
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    metis_tac[eval_base_place_preserves_scopes_dom] >>
  drule tuple_place_target_frame >> strip_tac >>
  drule_all wb_frame_local_regions >> strip_tac >>
  fs[target_post_def] >> disj2_tac >> disj2_tac >>
  qexistsl [`aid`, `b`, `sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem tuple_immutable_owned_target_pending:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_post ctx func cenv cx es sp sa s0 ee pv vt r s /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sp.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) /\
  i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
  val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory
Proof
  strip_tac >> fs[tuple_place_head_def] >>
  `val_in_memory (EL j ltvs) (EL j vs)
    (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s0.vs_memory` by simp[] >>
  `val_wf (EL j ltvs) (EL j vs)` by
    (irule aug_place_tuple_wf_project >>
     gvs[vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  `SUM (MAP type_memory_size (TAKE j ltvs)) + type_memory_size (EL j ltvs)
     <= type_memory_size_list ltvs` by
    (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule tuple_element_interval >> simp[]) >>
  drule_all tuple_place_target_allocation >> strip_tac >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- simp[] >>
  qexistsl [`type_memory_size (EL j ltvs)`, `s0.vs_memory`] >> simp[] >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then
    [`w2n w + SUM (MAP type_memory_size (TAKE j ltvs)) - b`,
     `type_memory_size (EL j ltvs)`] mp_tac) >> simp[]
QED

(* An equal-layout ternary arm can retain a local pointer even though the
   tuple assignment's syntactic staging flag is false. This is a compiler
   interface probe, not a counterexample to the statement simulation. *)
Theorem tuple_immutable_ifexp_borrow_probe:
  ~is_memory_view (IfExp (TupleT [ArrayT (BaseT BoolT) (Fixed 1)]) c x y) /\
  ~EVERY is_word_type [ArrayT (BaseT BoolT) (Fixed 1)] /\
  compile_ifexp_arm cenv
    (TupleT [ArrayT (BaseT BoolT) (Fixed 1)])
    (TupleT [ArrayT (BaseT BoolT) (Fixed 1)]) vv = unwrap_value cenv vv
Proof
  simp[stmtLoweringTheory.is_memory_view_def,
       compileEnvTheory.is_word_type_def,
       exprLoweringTheory.compile_ifexp_arm_def,
       contextTheory.same_memory_layout_def, contextTheory.punnable_def]
QED
