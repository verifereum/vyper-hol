Theory entryRuntimeContextCode
Ancestors
  entryDallocaCoverage compileVyper loweringShapeProps loweringShapeSource
  supportedProgram supportedNames list

Theorem entry_runtime_context_no_dalloca:
  supported_program tops /\ runtime_bodies_shape_ok tops /\ lower_vyper_runtime_unit tops pol = SOME unit ==>
  !f. MEM f unit.cu_context.ctx_functions ==>
    ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
      (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  drule_all lower_vyper_runtime_unit_no_dalloca >>
  simp[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED
