(* Allocation-map frames and address bounds for reserved constructor memory. *)
Theory ctorDeployMemoryRunMemEntryShiftedFrame
Ancestors
  ctorDeployMemoryRunMemEntryShiftedFrontier ctorDeployMemoryFrontier
  allocaBudgetProps venomState arithmetic words

Theorem alloca_frontier_inv_from_frame:
  !k ctx fn site s t site'.
    alloca_frontier_inv_from k ctx fn site s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
    alloca_frontier_inv_from k ctx fn site' t
Proof
  rpt strip_tac >>
  gvs[alloca_frontier_inv_from_def, remaining_alloca_budget_def]
QED

Theorem alloca_frontier_inv_from_bound:
  !k ctx fn site s.
    alloca_frontier_inv_from k ctx fn site s ==>
    s.vs_alloca_next <= k + unit_alloca_budget ctx
Proof
  rpt strip_tac >> gvs[alloca_frontier_inv_from_def] >> decide_tac
QED

Theorem alloca_frontier_inv_from_word_bound:
  !k ctx fn site s.
    alloca_frontier_inv_from k ctx fn site s /\
    k + unit_alloca_budget ctx < dimword (:256) ==>
    s.vs_alloca_next < dimword (:256)
Proof
  rpt strip_tac >> drule alloca_frontier_inv_from_bound >> simp[]
QED

Theorem alloca_frontier_inv_from_slot_bound:
  !k ctx fn site s slot.
    alloca_frontier_inv_from k ctx fn site s /\
    k + unit_alloca_budget ctx < dimword (:256) /\
    slot + 32 <= s.vs_alloca_next ==>
    slot < dimword (:256)
Proof
  rpt strip_tac >> drule_all alloca_frontier_inv_from_word_bound >> simp[]
QED
