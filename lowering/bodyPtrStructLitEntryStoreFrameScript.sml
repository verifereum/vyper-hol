Theory bodyPtrStructLitEntryStoreFrame
Ancestors exprSimAggregateChildren loweringPosts bodyPtrDefs
  valueEncodingProps valueEncodingProofs compileEnv venomState finite_map

Theorem structlit_entry_store_register_frame:
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  (!x. x <> dst /\ x <> load ==> lookup_var x sf = lookup_var x s) /\
  ~not_fresh_at sb dst /\ ~not_fresh_at sb load ==>
  !x v. not_fresh_at sb x /\ lookup_var x t = SOME v ==>
    lookup_var x sf = SOME v
Proof
  simp[vv_post_def] >> metis_tac[]
QED

Theorem structlit_entry_store_allocas_frame:
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  sf.vs_allocas = s.vs_allocas ==>
  !aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
    FLOOKUP sf.vs_allocas aid = SOME b
Proof
  simp[vv_post_def] >> metis_tac[]
QED

Theorem structlit_entry_store_slice_frame:
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  sf.vs_memory = (mstore a w s).vs_memory /\
  FLOOKUP t.vs_allocas aid = SOME (b,N) /\ aid < sb.cs_next_id /\
  (!name lo sz. local_region ce es.scopes t name lo sz ==>
    b+N <= lo \/ lo+sz <= b) /\
  b <= p /\ p+len <= b+N /\ (p+len <= a \/ a+32 <= p) ==>
  mem_bytes_at p len sf.vs_memory = mem_bytes_at p len t.vs_memory
Proof
  strip_tac >> drule_all vv_post_old_buffer >> strip_tac >>
  drule (cj 1 mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`p`, `len`] mp_tac) >>
  simp[mstore_mem_bytes_at_disjoint]
QED

Theorem structlit_entry_store_locals_frame:
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  sf.vs_memory = (mstore a w s).vs_memory /\
  (!name lo sz. local_region ce es.scopes t name lo sz ==>
    lo+sz <= a \/ a+32 <= lo) ==>
  locals_kept ce es ee t sf
Proof
  strip_tac >> `locals_kept ce es ee t s` by fs[vv_post_def] >>
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[mstore_mem_bytes_at_disjoint]
QED
