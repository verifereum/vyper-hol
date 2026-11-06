Theory concretizePtrOwnedReadAudit
Ancestors concretizePtrHistoricalWriteExclusion concretizePtrOperationalBytes
  concretizePtrPairedFields concretizePtrPrefixLedger words

(* Diagnostic quotation only: this is NOT a theorem or an assumption. *)
val owned_read_recovery_candidate = ``
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
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
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
  read_byte (b+k) endpoint.po_state.vs_memory =
    read_byte (pa+k) at.po_state.vs_memory``;
