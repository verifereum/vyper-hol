Theory requestCutStaticObligations
Ancestors
  e2eProducers o1PipelineCorrect contextStaticAbortRel contextRawReachable
  contextCodegenRel codegenEntrySim o1PassContract unitMemInv staticAbortDefs

Theorem request_cut_static_obligations_at_fmp:
  o1_pipeline rp unit = SOME out /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  unit_shape_ok out.po_unit /\
  max_live_eom out.po_unit.cu_context = SOME eom /\
  mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
    lowered_mem_fact eom ctx fn inst s) out.po_unit.cu_context v /\
  v.vs_initial_fmp = n2w cpl.cp_initial_fmp ==>
  codegen_context_obligations_abort (raw_reachable v) out.po_unit.cu_context cpl /\
  codegen_reachability_package (raw_reachable v) out.po_unit.cu_context v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`rp`, `unit`, `out`, `cpl`, `v`]
    o1_pipeline_context_obligations_lowered_abort) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> conj_tac >- (
    fs[codegen_context_obligations_abort_def,
       codegen_memory_obligations_abort_def] >>
    metis_tac[raw_reachable_least]) >>
  fs[codegen_reachability_package_def, raw_reachable_package_iff] >>
  metis_tac[]
QED
