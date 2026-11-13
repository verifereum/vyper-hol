(* Suspended phase endpoints are disjoint from current-owner allocations. *)
Theory readonlyInvokeCopyFwdSavedPhaseGuard
Ancestors
  readonlyInvokeCopyFwdHistoryStackAlignment readonlyInvokeCopyFwdHistoryPhase
  occurrenceGeometry
  o1LowerDloadOccurrence finite_map list pred_set pair

Theorem ricf_phase_entry_saved_copy_exclusion:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,pre) /\
  pre <> [] /\ FLOOKUP B (a,did) = SOME (db,len) ==>
  !k. k < p.rpe_size ==>
    ~(db <= p.rpe_db+k /\ p.rpe_db+k < db+len) /\
    ~(db <= p.rpe_sb+k /\ p.rpe_sb+k < db+len)
Proof
  simp[ricf_phase_entry_def] >> strip_tac >> gen_tac >> disch_tac >>
  drule ricf_history_cursor_endpoint_owners >> strip_tac >>
  drule occ_frame_reachable_owner_fresh >> simp[] >> strip_tac >>
  `MEM (EL (LENGTH pre - 1) U) U` by
    (irule EL_MEM >> Cases_on `pre` >> gvs[]) >>
  `(a,did) <> p.rpe_dst /\ (a,did) <> p.rpe_src` by
    (gvs[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  Cases_on `len = 0` >- gvs[] >>
  `0 < len` by decide_tac >>
  `db+len <= p.rpe_db \/ p.rpe_db+p.rpe_size <= db` by
    metis_tac[occurrence_geometry_sites_disjoint] >>
  `db+len <= p.rpe_sb \/ p.rpe_sb+p.rpe_size <= db` by
    metis_tac[occurrence_geometry_sites_disjoint] >>
  decide_tac
QED
