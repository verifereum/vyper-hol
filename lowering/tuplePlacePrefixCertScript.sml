(* Snapshot ownership is separate from loaded values and tuple bytes. *)
Theory tuplePlacePrefixCert
Ancestors
  tuplePlaceSnapshot loweringPosts valueEncoding venomState compileEnv
  vyperValue vyperTypeSystem list

Definition tuple_place_snapshot_def:
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs (w:256 word) s <=>
    EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      lo <= aid /\ aid < hi /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) \/
    (?n b sz. ltys = tys /\ local_region cenv es.scopes s n b sz /\
      b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
      local_path_at cenv cx n (w2n w-b) (TupleTV ltvs))
End

Theorem tuple_place_snapshot_words:
  EVERY is_word_type ltys ==>
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s
Proof simp[tuple_place_snapshot_def]
QED

Theorem tuple_place_snapshot_zero:
  type_memory_size_list ltvs = 0 ==>
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s
Proof simp[tuple_place_snapshot_def]
QED

Theorem tuple_place_snapshot_owned:
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ lo <= aid /\ aid < hi /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) ==>
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s
Proof rw[tuple_place_snapshot_def] >> metis_tac[]
QED

Theorem tuple_place_snapshot_borrowed:
  ltys = tys /\ local_region cenv es.scopes s n b sz /\
  b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
  local_path_at cenv cx n (w2n w-b) (TupleTV ltvs) ==>
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s
Proof rw[tuple_place_snapshot_def] >> metis_tac[]
QED

Theorem tuple_place_snapshot_cases:
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s ==>
  EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
  (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    lo <= aid /\ aid < hi /\ b <= w2n w /\
    w2n w + type_memory_size_list ltvs <= b+sz /\
    (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
      b+sz <= lb \/ lb+lsz <= b)) \/
  (?n b sz. ltys = tys /\ local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + type_memory_size_list ltvs <= b+sz /\
    local_path_at cenv cx n (w2n w-b) (TupleTV ltvs))
Proof simp[tuple_place_snapshot_def]
QED

Theorem tuple_place_snapshot_transport:
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s /\ hi <= hi' /\
  t.vs_allocas = s.vs_allocas /\
  (!n b sz. local_region cenv es.scopes t n b sz =
            local_region cenv es.scopes s n b sz) ==>
  tuple_place_snapshot cenv cx es lo hi' tys ltys ltvs w t
Proof
  rw[tuple_place_snapshot_def] >> simp[]
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  qexistsl [`n`, `b`, `sz`] >> gvs[]
QED

Theorem tuple_place_snapshot_hi_mono:
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s /\ hi <= hi' ==>
  tuple_place_snapshot cenv cx es lo hi' tys ltys ltvs w s
Proof
  strip_tac >> irule tuple_place_snapshot_transport >>
  goal_assum (drule_at Any) >> simp[] >> qexists `s` >> simp[]
QED

Theorem tuple_place_snapshot_word_probe:
  tuple_place_snapshot cenv cx es lo hi tys [BaseT BoolT] [BaseTV BoolT] w s
Proof irule tuple_place_snapshot_words >> EVAL_TAC
QED

Theorem tuple_place_snapshot_zero_probe:
  tuple_place_snapshot cenv cx es lo hi tys [TupleT []] [TupleTV []] w s
Proof irule tuple_place_snapshot_zero >> EVAL_TAC
QED

Theorem tuple_place_tuple_memory_transport:
  t.vs_memory = s.vs_memory /\ tuple_in_memory vs tvs a s.vs_memory ==>
  tuple_in_memory vs tvs a t.vs_memory
Proof
  simp[]
QED
