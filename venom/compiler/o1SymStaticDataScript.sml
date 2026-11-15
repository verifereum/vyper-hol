(* Byte-only data is unchanged by the generic pipeline's label maps. *)
Theory o1SymStaticData
Ancestors
  venomPipelineDriver venomPipelineRunner venomFnScheduleRunner
  unitLabelMap unitLabelMapIdentity fcgPruning venomCompilerTypes asmIR list finite_map

Theorem map_unit_data_section_bytes_only:
  EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    section.ds_items ==>
  map_unit_data_section lm section = section
Proof
  strip_tac >> simp[map_unit_data_section_def] >>
  `MAP (map_unit_data_item lm) section.ds_items = section.ds_items` by
    (irule MAP_eq_self >> fs[EVERY_MEM] >>
     Cases >> simp[] >> strip_tac >>
     first_x_assum (qspec_then `DataLabel s` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem apply_resolved_unit_label_map_bytes_only:
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  (apply_resolved_unit_label_map lm unit).cu_data_segment = unit.cu_data_segment
Proof
  strip_tac >> simp[apply_resolved_unit_label_map_def] >>
  irule MAP_eq_self >> fs[EVERY_MEM] >> rpt strip_tac >>
  irule map_unit_data_section_bytes_only >> simp[EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Theorem apply_unit_label_map_bytes_only:
  apply_unit_label_map lm unit = SOME unit' /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  simp[apply_unit_label_map_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> irule apply_resolved_unit_label_map_bytes_only >> simp[]
QED

Theorem run_configured_fn_passes_bytes_only:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  simp[run_configured_fn_passes_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule apply_unit_label_map_bytes_only >> simp[]
QED

Theorem run_named_fn_schedules_bytes_only:
  !names unit supply unit' supply'.
  run_named_fn_schedules runner rpolicy passes names unit supply =
    SOME (unit',supply') /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  Induct >> simp[run_named_fn_schedules_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all run_configured_fn_passes_bytes_only >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem run_mapped_functions_bytes_only:
  run_mapped_functions rpolicy pass unit supply = SOME (unit',supply') /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  simp[run_mapped_functions_def] >>
  metis_tac[run_named_fn_schedules_bytes_only]
QED

Theorem run_callee_first_bytes_only:
  run_callee_first rpolicy passes names unit supply = SOME (unit',supply') /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  simp[run_callee_first_def] >>
  metis_tac[run_named_fn_schedules_bytes_only]
QED

Theorem run_pipeline_stage_bytes_only:
  run_pipeline_stage rpolicy stage unit supply = SOME (unit',supply') /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  Cases_on `stage` >> simp[run_pipeline_stage_def] >>
  metis_tac[run_mapped_functions_bytes_only]
QED

Theorem run_pipeline_stages_bytes_only:
  !stages unit supply unit' supply'.
  run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  unit'.cu_data_segment = unit.cu_data_segment
Proof
  Induct >> simp[run_pipeline_stages_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all run_pipeline_stage_bytes_only >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem run_venom_pipeline_bytes_only:
  !mem_ok calling_ok post_ok rpolicy spec unit out.
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
    ds.ds_items) unit.cu_data_segment ==>
  out.po_unit.cu_data_segment = unit.cu_data_segment
Proof
  simp[run_venom_pipeline_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `pre_unit.cu_data_segment = unit.cu_data_segment` by
    metis_tac[run_pipeline_stages_bytes_only] >>
  qpat_x_assum `run_callee_first _ _ _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `run_callee_first _ _ _ walk_unit _` >>
  `walk_unit.cu_data_segment = unit.cu_data_segment` by
    (simp[Abbr `walk_unit`] >>
     Cases_on `spec.ps_prune_unreachable` >>
     simp[prune_unit_fcg_unreachable_fields]) >>
  strip_tac >> drule run_callee_first_bytes_only >> simp[] >>
  strip_tac >> drule run_pipeline_stages_bytes_only >> simp[]
QED
