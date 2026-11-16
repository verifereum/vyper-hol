Theory o1CodeEndConcretizeTransport
Ancestors
  o1CodeEndConcretizeObservation o1CodeEndConcretizeContract
  o1PassContract codegenSymRel

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
