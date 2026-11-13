Theory lowerDloadObservationBounds
Ancestors
  lowerDloadOwnership lowerDloadReachability lowerDloadTargetGeometry
  lowerDloadAllocation lowerDloadRelocation unitMemInv o1PassContract
  lowerDloadDefs ptrDiscipline finite_map list pred_set words

Theorem ld_annotated_headroom:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s ==>
  dload_headroom_ok C fn i s
Proof
  strip_tac >> drule ld_annotated_erasure >> strip_tac >>
  `raw_reachable vs0 C fn i s` by metis_tac[ld_frame_reachable_raw] >>
  fs[mem_inv_raw_reachable] >> metis_tac[]
QED

Theorem ld_observed_site_endpoints:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  callee_first names C.ctx_functions /\ ld_stack_origin vs0 C stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) ==>
  !owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bs+sz < dimword(:256) /\ bt+sz < dimword(:256)
Proof
  strip_tac >>
  `dload_headroom_ok C fn i s` by metis_tac[ld_annotated_headroom] >>
  `t.vs_alloca_next < dimword(:256)` by
    (drule_all ld_charged_frontier_budget >> simp[]) >>
  `s.vs_alloca_next < dimword(:256)` by
    (fs[dload_headroom_ok_def] >> decide_tac) >>
  rpt strip_tac >>
  `bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next` by metis_tac[] >>
  decide_tac
QED
