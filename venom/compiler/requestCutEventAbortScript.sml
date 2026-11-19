Theory requestCutEventAbort
Ancestors
  requestCutNativeEventCover dftGasInvReachSlice dftGasInvPrefixRun
  dftGasOracleDefs venomExecSemantics venomInst venomState venomWf list arithmetic

Theorem inv_ev_prefix_split_at[local]:
  !m n s t. inv_ev_prefix orc p d ctx bb (m + n) s t ==>
    ?u. inv_ev_prefix orc p d ctx bb m s u /\ inv_ev_prefix orc p d ctx bb n u t
Proof
  Induct >> simp[ADD_CLAUSES, inv_ev_prefix_suc] >> metis_tac[]
QED

Theorem event_visit_after_abort_impossible:
  EVERY wf_function C.ctx_functions /\
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C.ctx_functions /\ wf_function fn /\
  ev_reachable orc initial C p d fn x s /\
  ev_reachable orc initial C p d fn i t /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx < t.vs_inst_idx /\
  (!fuel. ev_step orc p d fuel C x s = Abort ab post) ==> F
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `ev_reachable orc initial C p d fn x s`
    (mp_tac o MATCH_MP inv_ev_reachable_slice) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`before`, `entry`, `first`, `bb`, `m`] strip_assume_tac) >>
  qpat_assum `ev_reachable orc initial C p d fn i t`
    (mp_tac o MATCH_MP inv_ev_reachable_slice) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`before'`, `entry'`, `first'`, `bb'`, `n`] strip_assume_tac) >>
  `entry.vs_current_bb = entry'.vs_current_bb` by metis_tac[] >>
  `bb = bb'` by gvs[] >>
  `first = first'` by gvs[] >>
  `entry = entry'` by metis_tac[request_cut_event_visit_unique] >>
  `m < n` by gvs[] >>
  `m + (n - m) = n` by decide_tac >>
  `?u. inv_ev_prefix orc p d C bb m entry u /\
       inv_ev_prefix orc p d C bb (n - m) u t` by
    (irule inv_ev_prefix_split_at >> gvs[]) >>
  `u = s` by metis_tac[inv_ev_prefix_unique] >>
  Cases_on `n - m` >> gvs[inv_ev_prefix_suc] >>
  metis_tac[]
QED
