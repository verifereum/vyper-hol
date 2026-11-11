(* Delayed memory reads use whole local regions, including length words.
   The pure-local posts interface is supplied by the seam, not imported. *)
Theory exprExtRequestDelayed
Ancestors
  exprExtRequestLocalProbe exprExtRequestReadProbe exprSimProps
  loweringPosts valueEncodingProofs

Theorem extrequest_local_read_kept:
  (!n b sz. local_region cenv es.scopes s0 n b sz ==>
     mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  local_region cenv es.scopes s0 name b0 sz0 /\
  b0 <= off /\ off + val_footprint tv v <= b0 + sz0 /\
  val_in_memory tv v off s0.vs_memory /\ val_wf tv v ==>
  val_in_memory tv v off s.vs_memory
Proof
  strip_tac >> irule val_in_memory_footprint_agree >>
  conj_tac >- simp[] >> qexists_tac `s0.vs_memory` >> simp[] >>
  `mem_bytes_at b0 sz0 s.vs_memory =
   mem_bytes_at b0 sz0 s0.vs_memory` by metis_tac[] >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  metis_tac[]
QED

(* In particular, the first unused nested-array slot remains intact;
   preserving only the outer value would not give this fact. *)
Theorem extrequest_nested_local_read_kept[local]:
  (!n b sz. local_region cenv es.scopes s0 n b sz ==>
     mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  local_region cenv es.scopes s0 name b0 sz0 /\
  b0 <= off /\ off + 64 <= b0 + sz0 ==>
  mem_word_at (off + 32) s.vs_memory =
    mem_word_at (off + 32) s0.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b0 sz0 s.vs_memory =
   mem_bytes_at b0 sz0 s0.vs_memory` by metis_tac[] >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum (qspec_then `off + 32` mp_tac) >> simp[]
QED

(* Placement, not an assumed local provenance, selects the protected region.
   The allocation alternative is already covered by the ordinary vv_post. *)
Theorem extrequest_memory_read_kept:
  vv_at cenv cx ty sa sm ee result (LocatedValue ty p) s0 /\
  vv_holds cenv cx ty result (LocatedValue ty p) ee s0 /\
  p.ptr_location = LocMemory /\
  read_result cx result ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s0 = SOME w /\
  vv_post ctx func cenv cx e ee sm sn s0 ee' result' vv s /\
  (!n b sz. local_region cenv ee.scopes s0 n b sz ==>
     mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
  val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >>
  `val_in_memory tv v (w2n w) s0.vs_memory` by
    gvs[vv_holds_def] >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >>
  gvs[]
  >- (irule val_in_memory_footprint_agree >> conj_tac >- simp[] >>
      qexists_tac `s0.vs_memory` >> simp[] >>
      `mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory` by
        (gvs[vv_post_def] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> strip_tac >> metis_tac[])
  >- metis_tac[extrequest_local_read_kept]
  >> irule val_in_memory_footprint_agree >> conj_tac >- simp[] >>
  qexists_tac `s0.vs_memory` >> simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED
