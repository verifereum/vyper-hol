Theory concretizePtrMloadExecution
Ancestors concretizePtrMloadRecovery concretizePtrMloadEndpoint
  concretizePtrMixedLoadTransport concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrOpaqueRetpc ptrDiscipline
  venomExecSemantics venomState list words arithmetic

Theorem ptr_paired_mload_execution_back:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt ==>
  !fuel t'. step_inst fuel C' a.po_inst at.po_state = OK t' ==>
    ?s'. step_inst fuel C a.po_inst a.po_state = OK s' /\
      ptr_mixed_vars births positions (step_prov PT TG a.po_inst s')
        (step_taint a.po_inst a.po_state s' a.po_taint)
        a.po_fn at.po_fn s' t'
Proof
  strip_tac >>
  drule_all ptr_paired_mload_endpoint_inputs >> strip_tac >>
  `!j. j < 32 /\ w2n x + j NOTIN a.po_taint.t_mem ==>
     read_byte (w2n x+j) a.po_state.vs_memory =
       read_byte (w2n y+j) at.po_state.vs_memory` by
    (drule ptr_paired_mload_masked_bytes >> simp[] >> metis_tac[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state` by
    (drule ptr_paired_prefix_endpoint >> strip_tac >> fs[ptr_paired_sample_def]) >>
  rpt strip_tac >>
  irule ptr_mixed_mload_transport_back >> simp[] >> metis_tac[ADD_COMM]
QED
