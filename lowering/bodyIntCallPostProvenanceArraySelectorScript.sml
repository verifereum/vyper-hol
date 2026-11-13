(* Actual-index reconstruction boundaries for noncapturing array selection. *)
Theory bodyIntCallPostProvenanceArraySelector
Ancestors
  bodyIntCallPostProvenanceArrayMemoryFrame
  bodyIntCallPostProvenanceArrayImmutableFrame
  bodyIntCallPostProvenanceArrayLiveSource bodyIntCallPostProvenanceArrayCode
  bodyIntCallPostProvenanceArrayElement bodyIntCallPostProvenanceSelectors
  exprSimSubscriptArrayFrame exprSimSubscriptArraySource vyperState pair
  loweringPosts exprSimProps valueEncodingProofs valueEncodingDefs

Theorem immutable_holds_source_frame[local]:
  immutable_holds ce cx ty r w es s /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  immutable_holds ce cx ty r w ee t
Proof
  strip_tac >>
  `FST (read_result cx r ee) = FST (read_result cx r es)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `SND (read_result cx r ee) = ee` by
    (Cases_on `read_result cx r ee` >> drule read_result_state >> simp[]) >>
  gvs[immutable_holds_def] >>
  qexistsl [`name`, `off`, `itv`, `iv`, `k`, `v`] >> simp[] >>
  metis_tac[PAIR, FST, SND]
QED

Theorem vv_holds_located_code_source_frame[local]:
  vv_holds ce cx ty r (LocatedValue ann p) es s /\
  p.ptr_location = LocCode /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand t = SOME w) /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  vv_holds ce cx ty r (LocatedValue ann p) ee t
Proof
  strip_tac >> gvs[vv_holds_def] >>
  drule_all immutable_holds_source_frame >> simp[]
QED

Theorem provenance_memory_value_frame[local]:
  intcall_vv_provenance ce cx ty sa sb es raw (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  expr_sim_inv ce cx env es /\ wb_frame ce es ee sb s t /\
  ee.scopes = es.scopes /\ local_ptrs_reserved ce sb /\
  local_ptrs_rel func ce ee.scopes t ==>
  val_in_memory tv v (w2n w) t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyIntCallProducerInterfaceTheory.intcall_vv_provenance_def]) >>
  strip_tac >> qpat_x_assum `!op. _` (qspec_then `p.ptr_operand` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >~ [`FLOOKUP s.vs_allocas aid = SOME (b,sz)`]
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
      irule val_in_memory_footprint_agree >>
      simp[] >> qexists `s.vs_memory` >> simp[] >>
      drule mem_bytes_at_agree_window >> strip_tac >>
      first_x_assum irule >> simp[]) 
  >~ [`val_footprint tv v = 0`]
  >- (irule val_in_memory_footprint_agree >>
      simp[mem_bytes_at_def] >> qexists `s.vs_memory` >> simp[])
  >~ [`local_val_at ce cx n (w2n w - b) tv v`]
  >- (`mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
        (irule locals_kept_dynarray_free_value >>
         goal_assum (drule_at Any) >> gvs[wb_frame_def] >> metis_tac[]) >>
      irule val_in_memory_footprint_agree >>
      simp[] >> qexists `s.vs_memory` >> simp[]) >>
  rename1 `lookup_var root s = SOME rootword` >>
  `lookup_var root t = SOME rootword` by
    (gvs[wb_frame_def, loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all bodyIntCallLocalFrameTheory.local_ptrs_rel_sub_layout >>
  simp[arithmeticTheory.ADD_COMM]
QED
