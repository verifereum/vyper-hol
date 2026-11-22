(* Raw source-unit invariants for the linked O1 pipeline. *)
Theory linkedRawUnitShape
Ancestors
  compileUnit vyperCompiler vyperLoweringCorrect deployUnitProducers
  o1PassContract venomInst list

Theorem lower_vyper_runtime_unit_raw_shape_mods:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit ==>
  lowering_context_ok unit.cu_context /\ unit_defs_reach_uses unit /\
  EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
  unit_fmp_unsealed unit
Proof
  simp[lower_vyper_runtime_unit_mods_def] >>
  pairarg_tac >> simp[bool_case_eq] >> strip_tac >> gvs[]
  >- (`lowering_context_ok unit.cu_context` by
        (drule run_grouped_lowering_context >> simp[]) >>
      drule lowering_context_ok_defs_reach_uses >> simp[unit_defs_reach_uses_def] >>
      strip_tac >>
      qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
      simp[run_grouped_lowering_def, extract_context_with_internals_def,
           mk_venom_context_def, unit_fmp_unsealed_def] >>
      pairarg_tac >> gvs[AllCaseEqs()] >> strip_tac >>
      gvs[mk_raw_function_def] >>
      drule package_internal_blocks_raw_defaults >>
      simp[EVERY_MEM, function_raw_metadata_defaults_def]) >>
  drule run_lowering_context_ok >> strip_tac >>
  drule lowering_context_ok_defs_reach_uses >>
  drule run_lowering_eom_none >> drule run_lowering_fmp_unsealed >>
  simp[unit_defs_reach_uses_def]
QED

Theorem lower_vyper_deploy_unit_raw_shape_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME unit ==>
  lowering_context_ok unit.cu_context /\ unit_defs_reach_uses unit /\
  EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
  unit_fmp_unsealed unit
Proof
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[bool_case_eq] >> strip_tac >>
  drule run_deploy_lowering_context_ok >> strip_tac >>
  drule lowering_context_ok_defs_reach_uses >> simp[unit_defs_reach_uses_def] >>
  strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, extract_context_with_internals_def,
       install_immutable_reservation_def, mk_venom_context_def,
       unit_fmp_unsealed_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> strip_tac >>
  gvs[mk_raw_function_def] >>
  drule package_internal_blocks_raw_defaults >>
  simp[EVERY_MEM, function_raw_metadata_defaults_def]
QED
