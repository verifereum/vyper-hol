Theory concretizeAnalysisStageSizes
Ancestors
  concretizeAnalysisSizeReach concretizeAnalysisSizes frameAllocationSizes
  o1PassContract unitTransformDefs list

Theorem o1_run_cache_sizes_ok_static[local]:
  (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0) ==> cache_sizes_ok M vs0
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def, cache_sizes_ok_empty]
QED

Theorem o1_run_cache_sizes_ok:
  o1_run_state_ok vs0 ==> cache_sizes_ok M vs0
Proof
  mp_tac o1_run_cache_sizes_ok_static >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem o1_frame_source_sizes_current_static[local]:
  (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0) /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  cache_sizes_ok (source_alloca_sizes fn) s
Proof
  metis_tac[frame_source_sizes_current, o1_run_cache_sizes_ok_static]
QED

Theorem o1_frame_source_sizes_current:
  o1_run_state_ok vs0 /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  cache_sizes_ok (source_alloca_sizes fn) s
Proof
  mp_tac o1_frame_source_sizes_current_static >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem o1_frame_source_sizes_saved_static:
  (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0) /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ MEM f stk ==>
  cache_sizes_ok (source_alloca_sizes f.cf_fn) f.cf_state
Proof
  metis_tac[frame_source_sizes_saved, o1_run_cache_sizes_ok_static]
QED

Theorem o1_frame_source_sizes_saved:
  o1_run_state_ok vs0 /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ MEM f stk ==>
  cache_sizes_ok (source_alloca_sizes f.cf_fn) f.cf_state
Proof
  mp_tac o1_frame_source_sizes_saved_static >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem o1_frame_source_sizes_lookup_static:
  (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0) /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  FLOOKUP (source_alloca_sizes fn) aid = SOME sz
Proof
  metis_tac[o1_frame_source_sizes_current_static, cache_sizes_ok_lookup]
QED

Theorem o1_frame_source_sizes_lookup:
  o1_run_state_ok vs0 /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  FLOOKUP (source_alloca_sizes fn) aid = SOME sz
Proof
  mp_tac o1_frame_source_sizes_lookup_static >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED
