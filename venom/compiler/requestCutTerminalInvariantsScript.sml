Theory requestCutTerminalInvariants
Ancestors
  requestCutCoveredInvariants requestCutNativeEventCover requestCutNativeAbortVisit
  requestCutAbortBound jointRequestCut frameJointTrace frameJointTransition frameRawProjection dftGasFromListTraceDefs dftContractGas
  dftGasOracleDefs passSimulationDefs o1PassContract unitMemInv venomPassSchedule venomExecSemantics
  contextCodegenRel codegenSymRel staticAbortDefs unitShapeDefs venomInst venomState list

(* A primitive abort bounds the request count at every native visit. *)
Theorem request_cut_abort_invariants:
  EVERY wf_function C.ctx_functions /\
  raw_reachable v C fn inst s /\
  LENGTH s.vs_requests <= k /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Abort ab post /\
  mem_inv (\ctx fn j t. LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t ==>
    lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn j t) C v /\
  (guarded ==> code_end_offset_ok (\ctx fn j t. raw_reachable v ctx fn j t /\
    LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t) C) ==>
  mem_inv (\ctx fn j t. in_static_abort_prefix fn t \/
    lowered_mem_fact eom ctx fn j t) C v /\
  (guarded ==> code_end_offset_ok
    (\ctx fn j t. raw_reachable v ctx fn j t /\ ~in_static_abort_prefix fn t) C)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_reachable_joint_trace >> strip_tac >>
  `!g j t. raw_reachable v C g j t ==> LENGTH t.vs_requests <= k` by
    (rpt strip_tac >> drule_all joint_trace_primitive_abort_request_bound >>
     decide_tac) >>
  fs[mem_inv_raw_reachable, lowered_mem_fact_def, code_end_offset_ok_def] >>
  metis_tac[]
QED
