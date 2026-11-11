Theory entryReachBodyFmp
Ancestors
  loweringShapeProps loweringShapeSource o1PipelineCorrect ptrDiscipline
  exprLoweringProps supportedProgram supportedNames moduleLowering list

Theorem entry_runtime_no_dalloca:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops ==> ~ctx_has_dalloca unit.cu_context
Proof
  strip_tac >> irule o1_source_unit_ok_no_dalloca >>
  irule lower_vyper_runtime_unit_source_unit_ok_shape >>
  goal_assum $ drule_at Any >>
  reverse conj_tac >- metis_tac[supported_program_runtime_bodies_shape_ok] >>
  irule supported_names_internal_names_distinct >>
  gvs[supported_program_def, supported_declaration_names_def]
QED

Theorem entry_no_dalloca_fmp_room[local]:
  ~ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
  fmp_room ctx func s
Proof
  simp[ctx_has_dalloca_def, fmp_room_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem entry_runtime_fmp_room:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ MEM func unit.cu_context.ctx_functions ==>
  fmp_room unit.cu_context func s
Proof
  metis_tac[entry_runtime_no_dalloca, entry_no_dalloca_fmp_room]
QED
