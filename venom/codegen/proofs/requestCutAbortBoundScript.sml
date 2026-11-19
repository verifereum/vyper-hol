Theory requestCutAbortBound
Ancestors
  jointRequestCut requestCutNativeAbortVisit dftGasFromListLocator
  dftGasFromListTraceDefs frameJointTrace frameJointTransition frameRawProjection
  dftGasRequestObservation contextCodegenRel venomExecSemantics
  venomState venomInst venomWf list rich_list

Theorem joint_trace_primitive_abort_request_bound:
  EVERY wf_function C.ctx_functions /\
  joint_trace vs0 C q0 es qs (JointConfig stk PG G tn fn inst s oms om hs h) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = Abort ab post /\
  raw_reachable vs0 C fn' inst' t ==>
  LENGTH t.vs_requests <= LENGTH s.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_reachable_joint_trace >> strip_tac >>
  `raw_reachable vs0 C fn inst s` by
    metis_tac[joint_trace_reachable, joint_config_raw] >>
  spose_not_then assume_tac >>
  `LENGTH s.vs_requests < LENGTH t.vs_requests` by decide_tac >>
  rename1 `joint_trace vs0 C r0 fs rs
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h')` >>
  mp_tac (Q.INST [`k` |-> `LENGTH s.vs_requests`,
    `fn` |-> `fn'`, `inst` |-> `inst'`, `last` |-> `t`,
    `q0` |-> `r0`, `es` |-> `fs`, `qs` |-> `rs`,
    `stk` |-> `stk'`, `PG` |-> `PG'`, `G` |-> `G'`, `tn` |-> `tn'`,
    `oms` |-> `oms'`, `om` |-> `om'`, `hs` |-> `hs'`, `h` |-> `h'`,
    `g` |-> `fn`, `j` |-> `inst`, `s` |-> `s`]
    raw_reachable_request_cut_visit) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`i`, `stki`, `PGi`, `Gi`, `tni`, `omsi`,
    `omi`, `hsi`, `hi`] strip_assume_tac) >>
  mp_tac (Q.INST [`n` |-> `i`, `ctx` |-> `C`, `q0` |-> `r0`, `es` |-> `fs`, `qs` |-> `rs`,
    `q` |-> `JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h'`]
    (SPEC_ALL joint_trace_edge_at)) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
  qpat_assum `EL i (r0::rs) = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
  rewrite_tac[Once joint_transition_cases] >>
  strip_tac >> gvs[step_inst_non_invoke]
QED

(* A primitive abort closes the native root run with the request history
   at the stopped cursor. *)
Theorem raw_reachable_primitive_abort:
  EVERY wf_function C.ctx_functions /\
  raw_reachable v C fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Abort ab post ==>
  ?n. run_context n C v = Abort ab post /\ post.vs_requests = s.vs_requests
Proof
  strip_tac >> drule_all raw_reachable_trace >> strip_tac >>
  `step_inst_base inst s = Abort ab post` by
    gvs[step_inst_non_invoke] >>
  drule_all native_trace_context_primitive_abort >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[step_inst_abort_requests]
QED
