Theory loadElimRoundWf
Ancestors
  loadElimInstWf loadElimActions loadElimStructure loadElimDefs
  analysisSimDefs passSimulationProps venomWf venomInst list indexedLists

Theorem le_old_transform_wf:
  !ctx actions result fn.
    le_supported_config ctx.lctx_config /\ wf_function fn ==>
    wf_function (analysis_function_transform NONE result
      (\ll inst. [load_elim_inst ctx actions ll inst]) fn)
Proof
  rpt strip_tac >> irule aft_singleton_preserves_wf >>
  simp[le_load_elim_inst_id, le_load_elim_inst_terminator,
       le_load_elim_inst_phi, le_load_elim_inst_terminator_unchanged]
QED
