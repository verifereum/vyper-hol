Theory concretizePtrMloadIntegrationAudit
Ancestors concretizePtrFixedReadRecovery concretizePtrOwnedReadAudit
  concretizePtrLoadTransport concretizePtrOpaqueRetpc
  concretizePtrMstoreProducer concretizeStepStructure concretizeStepShape
  concretizeStepCallChecks concretizeStepRetpc concretizeStageShape
  concretizePtrStagePlacements
  concretizePtrOwnerFloor ptrDiscipline list

(* Specification only: parsed/typechecked, NOT an assertion or theorem.
   Direct successor cursor normalization is included in this candidate. *)
val mload_prefix_extension_candidate = ``
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
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws``;

(* .63: specification only. No recovery/source-success premise, no theorem. *)
val mload_masked_bytes_candidate = ``
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
  a.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt /\
  a.po_inst.inst_operands = [op] /\
  eval_operand op a.po_state = SOME x /\ eval_operand op at.po_state = SOME y ==>
  !j. j < 32 /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x + j) a.po_state.vs_memory =
      read_byte (w2n y + j) at.po_state.vs_memory``;
