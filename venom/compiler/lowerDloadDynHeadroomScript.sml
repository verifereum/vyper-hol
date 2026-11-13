(*
 * The DLOAD headroom invariant against the dynamic floor: under DALLOCA
 * the alloca frontier, plus the DLOAD scratch still to come, stays at or
 * below the initial free memory pointer.  Kept below the o1 layer so the
 * pass proofs that reason about dyn_floor can use it.
 *)
Theory lowerDloadDynHeadroom
Ancestors
  lowerDloadDefs ptrDiscipline unitMemInv contextRawReachable ctxLookupAgree

Theorem ld_raw_dyn_headroom:
  mem_inv dload_headroom_ok C vs /\ raw_reachable vs C fn inst s ==>
  s.vs_alloca_next + 32 * ctx_dload_count C <= dyn_floor C vs
Proof
  strip_tac >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    metis_tac[raw_reachable_initial_fmp] >>
  `dload_headroom_ok C fn inst s` by
    (qpat_x_assum `mem_inv _ _ _` mp_tac >> simp[mem_inv_raw_reachable] >>
     metis_tac[]) >>
  fs[dload_headroom_ok_def, dyn_floor_def, ctx_has_dalloca_def] >>
  rw[] >> fs[] >>
  TRY (qpat_x_assum `s.vs_initial_fmp = _` SUBST_ALL_TAC) >> decide_tac
QED
