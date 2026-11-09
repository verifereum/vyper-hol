Theory exprPtrUnwrapAllocSeparation
Ancestors
  exprSimAlloc allocationPtr bufferAllocationExecution exprPtrUnwrapTypedSize
  exprLoweringProps loweringPosts compileEnv finite_map words

(* The actual allocation site can be reused; its base need not be the
   current allocation frontier. *)
Theorem unwrap_alloc_site_bound:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) ==>
  buffer_allocation_base s sm.cs_next_id + nb < dimword (:256)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`
  >- (simp[buffer_allocation_base_def] >>
      drule_all stmt_state_rel_alloca_fresh_bound >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME site` >>
  PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  simp[buffer_allocation_base_def]
QED

Theorem unwrap_alloc_old_entry_separation:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  vv_post ctx func cenv cx e es sa sm s0 es' result vv s /\
  nb < dimword (:256) /\ sa.cs_next_id <= sm.cs_next_id /\
  FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
  buffer_allocation_base s sm.cs_next_id + nb <= off \/
  off + len <= buffer_allocation_base s sm.cs_next_id
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `sm.cs_next_id <> aid` by decide_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  irule buffer_allocation_disjoint >> simp[] >>
  reverse conj_tac >- (qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >> drule_all stmt_state_rel_alloca_site_bound >> simp[]
QED

Theorem unwrap_alloc_typed_loop_bound:
  compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
  fn_has_code sm mid func /\ stmt_state_rel ctx func cenv cx es s /\
  type_memory_bytes cenv t = type_memory_size tv /\
  type_memory_size tv < 2**64 ==>
  buffer_allocation_base s sm.cs_next_id + 32 * type_slot_size tv < 2**256
Proof
  strip_tac >>
  `type_memory_bytes cenv t < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all unwrap_typed_buffer_bytes >> strip_tac >>
  drule_all unwrap_alloc_site_bound >>
  simp[wordsTheory.dimword_def]
QED
