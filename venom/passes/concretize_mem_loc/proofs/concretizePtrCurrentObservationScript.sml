Theory concretizePtrCurrentObservation
Ancestors
  concretizePtrCurrentRangeTransport concretizePtrObservationInterface concretizePtrStageBounds
  concretizePtrForwardingTransport concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrDeletedGapHistory concretizePtrChronologicalHistory
  concretizePtrSourceOwnership concretizePtrOwnershipErasure
  concretizePtrAllocationSize concretizePtrParamSupport
  concretizePtrPairedFields concretizePtrSharedFields
  concretizeStepStructure concretizeMemLocDefs
  venomExecProofs passSimulationDefs passSharedDefs unitLabelMapIdentity concretizePtrOpaqueRetpc
  lowerDloadDefs
  ptrDiscipline unitMemInv unitShapeDefs venomWf o1PassContract
  contextCodegenRel codegenRel memLocDefs pointerConfinedDefs
  venomInst list finite_map pred_set words arithmetic

Theorem ptr_paired_current_static_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ mem_inv dload_headroom_ok C vs /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  in_revert_forward at.po_fn at.po_state \/
  (!off len.
    MEM (off,len) (source_memory_read_ranges at.po_inst at.po_state ++
                  source_memory_write_ranges at.po_inst at.po_state) ==>
    len = 0 \/ off + len <= eom \/
    (w2n at.po_state.vs_initial_fmp <= off /\ off + len <= w2n at.po_state.vs_fmp))
Proof
  cheat
QED
