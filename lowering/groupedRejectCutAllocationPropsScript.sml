(* Allocation facts used by the grouped reject cut. *)
Theory groupedRejectCutAllocationProps
Ancestors
  allocaFrontierRoom allocaFrontierBound allocaSiteResource contextCodegenRel
  ptrDiscipline venomState words arithmetic

Theorem alloca_frontier_charge_frame:
  t.vs_alloca_next + pending_alloca_size fn t =
    s.vs_alloca_next + pending_alloca_size fn s /\
  alloca_frontier_inv ctx fn site s ==>
  alloca_frontier_inv ctx fn site t
Proof
  `!u. alloca_frontier_inv_from 0 ctx fn site u <=> alloca_frontier_inv ctx fn site u` by
    simp[alloca_frontier_inv_from_shift_def] >>
  pop_assum (fn zero => PURE_REWRITE_TAC [GSYM zero]) >>
  PURE_REWRITE_TAC [alloca_frontier_inv_from_def, ADD_CLAUSES,
    GSYM deploy_ctor_pending_alloca_eq] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem allocas_below_fmp_from_frontier:
  alloca_inv s /\ s.vs_alloca_next <= w2n s.vs_initial_fmp /\
  w2n s.vs_initial_fmp <= w2n s.vs_fmp ==>
  allocas_below_fmp s
Proof
  strip_tac >> simp[allocas_below_fmp_def] >> rpt strip_tac >>
  drule_all alloca_site_registered_below >> decide_tac
QED
