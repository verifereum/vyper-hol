Theory o1LowerDloadOccurrenceHeadroom
Ancestors
  o1LowerDloadRawBridge o1LowerDloadReadiness o1LowerDloadOccurrence
  o1PassContract lowerDloadDefs unitMemInv venomWf venomExecSemantics
  contextCodegenRel list words venomInst contextRawReachable ctxLookupAgree
  ptrDiscipline lowerDloadDynHeadroom

Theorem ld_occurrence_headroom:
  (!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f) /\
  mem_inv dload_headroom_ok C vs /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  s.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >> drule occ_frame_reachable_projection >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule_all ld_reachable_headroom >> simp[]
QED

Theorem ld_occurrence_alloca_headroom:
  (!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f) /\
  mem_inv dload_headroom_ok C vs /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s1 ==>
  s1.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >> drule occ_frame_reachable_projection >> strip_tac >>
  drule_all ld_frame_raw_stack >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule_all ld_alloca_successor_active >> strip_tac >>
  irule ld_next_headroom >> metis_tac[is_terminator_def]
QED

Theorem ld_ctx_shape_lookup_wf:
  o1_ctx_shape C /\ lookup_function name C.ctx_functions = SOME f ==>
  wf_function f
Proof
  simp[o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM f C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  metis_tac[o1_fn_shape_def]
QED

Theorem ld_occurrence_shape_headroom:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  s.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >> irule ld_occurrence_headroom >>
  metis_tac[ld_ctx_shape_lookup_wf]
QED

Theorem ld_occurrence_shape_alloca_headroom:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s1 ==>
  s1.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >> irule ld_occurrence_alloca_headroom >>
  metis_tac[ld_ctx_shape_lookup_wf]
QED

Theorem ld_occurrence_shape_dyn_headroom:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  s.vs_alloca_next + 32 * ctx_dload_count C <= dyn_floor C vs
Proof
  strip_tac >>
  `!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f` by
    metis_tac[ld_ctx_shape_lookup_wf] >>
  drule occ_frame_reachable_projection >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  irule ld_raw_dyn_headroom >> metis_tac[]
QED

Theorem ld_occurrence_shape_alloca_dyn_headroom:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s1 ==>
  s1.vs_alloca_next + 32 * ctx_dload_count C <= dyn_floor C vs
Proof
  strip_tac >>
  `!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f` by
    metis_tac[ld_ctx_shape_lookup_wf] >>
  drule occ_frame_reachable_projection >> strip_tac >>
  drule_all ld_frame_raw_stack >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule_all ld_alloca_successor_active >> strip_tac >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `raw_reachable vs C fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[raw_reachable_next] >>
  irule (ld_raw_dyn_headroom
           |> Q.INST [`s` |-> `s1 with vs_inst_idx := SUC s.vs_inst_idx`]
           |> SIMP_RULE (srw_ss()) []) >>
  metis_tac[]
QED

