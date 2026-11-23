Theory entryReachBodyFmp
Ancestors
  allocaFrontierRoom allocaFrontierBound entryDallocaCoverage
  ptrDiscipline exprLoweringProps venomInst list words arithmetic

(* The frontier invariant bounds the remaining static allocations. *)
Theorem entry_frontier_fmp_room:
  alloca_frontier_inv ctx fn site s /\
  s.vs_fmp = s.vs_initial_fmp /\
  (ctx_has_dalloca ctx ==> unit_alloca_budget ctx <= w2n s.vs_initial_fmp /\
    w2n s.vs_initial_fmp < 2 ** 254) ==>
  fmp_room ctx fn s
Proof
  strip_tac >>
  qpat_assum `alloca_frontier_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [alloca_frontier_inv_def]) >>
  Cases_on `ctx_has_dalloca ctx`
  >- (fs[fmp_room_def, deploy_ctor_pending_alloca_eq, unit_alloca_frame_def,
         deploy_ctor_alloca_size_eq] >>
      decide_tac) >>
  irule entryDallocaCoverageTheory.context_without_dalloca_fmp_room >>
  conj_tac >- (fs[ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  metis_tac[lookup_function_MEM]
QED
