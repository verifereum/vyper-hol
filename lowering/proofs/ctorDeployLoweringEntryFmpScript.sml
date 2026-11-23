(* Allocation room at the reached constructor entry. *)
Theory ctorDeployLoweringEntryFmp
Ancestors
  ctorDeployLoweringDefs exprLoweringProps o1PipelineCorrect
  ptrDiscipline allocaFrontierRoom allocaFrontierBound entryDallocaCoverage
  venomMemDefs words list arithmetic

Theorem deploy_entry_frontier_fmp_room:
  alloca_frontier_inv_from k ctx func site s /\
  s.vs_fmp = s.vs_initial_fmp /\
  (ctx_has_dalloca ctx ==>
    k + unit_alloca_budget ctx <= w2n s.vs_initial_fmp /\
    w2n s.vs_initial_fmp < 2 ** 254) ==>
  fmp_room ctx func s
Proof
  strip_tac >>
  qpat_assum `alloca_frontier_inv_from _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [alloca_frontier_inv_from_def]) >>
  Cases_on `ctx_has_dalloca ctx`
  >- (fs[fmp_room_def, deploy_ctor_pending_alloca_eq, unit_alloca_frame_def,
         deploy_ctor_alloca_size_eq] >> decide_tac) >>
  irule context_without_dalloca_fmp_room >>
  conj_tac >- (fs[ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  metis_tac[venomInstTheory.lookup_function_MEM]
QED

Theorem deploy_entry_frontier_allocas_below_fmp:
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  k + unit_alloca_budget ctx <= w2n s.vs_initial_fmp /\
  w2n s.vs_initial_fmp <= w2n s.vs_fmp ==>
  allocas_below_fmp s /\
  s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp
Proof
  strip_tac >>
  qpat_assum `alloca_frontier_inv_from _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [alloca_frontier_inv_from_def]) >>
  fs[alloca_inv_def, alloca_next_valid_def, allocas_below_fmp_def,
     deploy_ctor_pending_alloca_eq] >>
  rpt strip_tac >> res_tac >> decide_tac
QED
