Theory bodyFullRawCallCallFrame
Ancestors
  robustCopyTransportPtr valueEncodingProps bodyPtrDefs pred_set ptrDiscipline
  venomInst finite_map localPtrsProps loweringSlice venomMemProps
  appendStorageGhostPtr exprSimProps decoderGhostFramePtr

Triviality robust_val_clean_write_frame:
  val_wf tv v /\
  (p + val_footprint tv v <= dst \/ dst + LENGTH bytes <= p) /\
  (!i. ~(dst <= i /\ i < dst + LENGTH bytes) ==> (i IN dirty' <=> i IN dirty)) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==> val_in_memory tv v p mem) ==>
  !mem. mem_agree_outside dirty'
    (write_memory_with_expansion dst bytes s).vs_memory mem ==>
    val_in_memory tv v p mem
Proof
  rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `(write_memory_with_expansion dst bytes s).vs_memory`,
    `dirty`, `dirty'`, `{i | dst <= i /\ i < dst + LENGTH bytes}`] >>
  simp[] >> rpt strip_tac >>
  irule write_memory_mem_bytes_at_disjoint >> decide_tac
QED

Triviality local_robust_clean_write_frame:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem) /\
  (!name a len. local_region cenv scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) /\
  (!i. ~(dst <= i /\ i < dst + LENGTH bytes) ==> (i IN dirty' <=> i IN dirty)) ==>
  !mem. mem_agree_outside dirty'
    (write_memory_with_expansion dst bytes s).vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> simp[]) >>
  irule robust_val_clean_write_frame >> simp[] >>
  qexistsl_tac [`bytes`, `dirty`, `dirty'`, `dst`, `s`] >> simp[] >>
  `val_footprint entry.type entry.value <= sz` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  `local_region cenv scopes s name (w2n w) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem raw_call_clean_write_ghost_at:
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP HG x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x) /\
    lookup_var x u = lookup_var x s) /\
  ee.scopes = es.scopes /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  un.t_mem = tn.t_mem DIFF {i | dst <= i /\ i < dst + LENGTH bytes} /\
  (bytes = [] \/ lo <= dst) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  stor_taint_ok_at D un u ==>
  ghost_inv_at D lo d cenv cx ee HG un u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[] >> Cases_on `bytes = []`
     >- (gvs[venomStateTheory.write_memory_with_expansion_def,
              valueEncodingProofsTheory.mem_bytes_at_append_zero,
              listTheory.TAKE_DROP] >>
         IF_CASES_TAC >>
         simp[valueEncodingProofsTheory.mem_bytes_at_append_zero]) >>
     irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
     gvs[]) >>
  qpat_x_assum `bytes = [] \/ lo <= dst` kall_tac >>
  fs[bodyPtrDefsTheory.ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by
        metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
      qpat_x_assum `!name entry p sz. _` drule >> strip_tac >> conj_tac
      >- (irule appendStorageGhostPtrTheory.ptr_covers_old_transport >>
          goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      irule local_robust_clean_write_frame >>
      first_assum (irule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
      first_assum (irule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
      qexistsl_tac [`dst`, `un.t_mem`, `tn.t_mem`, `bytes`] >>
      gvs[] >> metis_tac[]) >>
  rpt conj_tac
  >- (Cases_on `d` >> fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def] >>
      metis_tac[appendStorageGhostPtrTheory.ptr_covers_old_transport])
  >- metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]
  >> gvs[ptrDisciplineTheory.allocas_from_def] >> gvs[]
QED
