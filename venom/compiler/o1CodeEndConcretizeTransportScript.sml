Theory o1CodeEndConcretizeTransport
Ancestors
  o1CodeEndConcretizeObservation o1CodeEndConcretizeContract
  o1PassContract codegenSymRel unitTransformDefs venomPassSchedule

Theorem concretize_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 2 o1_fn_passes)
    (o1_walk_view rpolicy 2) (o1_pre 2)
    (\C s. o1_inv D 2 C s /\ ~ctx_has_dalloca C /\
      code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 3 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  irule concretize_code_end_contract_from_reflection >>
  metis_tac[concretize_codecopy_reflect]
QED

Theorem concretize_code_end_offset_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\ o1_inv D 2 C vs /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  code_end_offset_ok (raw_reachable vs) C ==>
  code_end_offset_ok (raw_reachable vs) C'
Proof
  strip_tac >> simp[code_end_offset_ok_def] >> rpt strip_tac >>
  drule_all concretize_codecopy_reflect_static >> strip_tac >>
  fs[code_end_offset_ok_def] >> metis_tac[]
QED
