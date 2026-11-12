(* Registered allocation windows are protected from distinct scratch sites. *)
Theory registeredAllocationWindow
Ancestors
  allocaSiteResource venomMemDefs pred_set

Theorem registered_allocation_subwindow_disjoint:
  alloca_inv s /\ FLOOKUP s.vs_allocas parent = SOME (p,n) /\
  parent NOTIN ids /\ k <= n ==>
  !id b sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (p,k) (b,sz)
Proof
  rpt strip_tac >>
  `parent <> id` by metis_tac[] >>
  `venomMemDefs$regions_disjoint (p,n) (b,sz)` by
    (irule alloca_site_registered_disjoint >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
