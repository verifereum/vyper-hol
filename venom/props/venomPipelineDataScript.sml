(* Byte-only data sections survive the actual pipeline's label-map updates. *)
Theory venomPipelineData
Ancestors
  venomPipelineDriver venomPipelineRunner venomFnScheduleRunner unitLabelMap
  fcgPruning venomCompilerTypes asmIR list finite_map

Theorem map_unit_data_section_data_bytes[simp]:
  map_unit_data_section lm
    <| ds_label := label; ds_items := [DataBytes bytes] |> =
    <| ds_label := label; ds_items := [DataBytes bytes] |>
Proof
  simp[map_unit_data_section_def]
QED

Theorem apply_resolved_unit_label_map_data_bytes_section:
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    (apply_resolved_unit_label_map lm unit).cu_data_segment
Proof
  strip_tac >> simp[apply_resolved_unit_label_map_def, MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem apply_unit_label_map_data_bytes_section:
  apply_unit_label_map lm unit = SOME unit' /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  simp[apply_unit_label_map_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> irule apply_resolved_unit_label_map_data_bytes_section >> simp[]
QED

Theorem run_configured_fn_passes_data_bytes_section:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  simp[run_configured_fn_passes_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule apply_unit_label_map_data_bytes_section >> simp[]
QED

Theorem run_named_fn_schedules_data_bytes_section:
  !names unit supply unit' supply'.
  run_named_fn_schedules runner rpolicy passes names unit supply =
    SOME (unit',supply') /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  Induct >> simp[run_named_fn_schedules_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule run_configured_fn_passes_data_bytes_section >>
  disch_then drule >> strip_tac >> first_x_assum irule >>
  metis_tac[]
QED

Theorem run_mapped_functions_data_bytes_section:
  run_mapped_functions rpolicy pass unit supply = SOME (unit',supply') /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  simp[run_mapped_functions_def] >>
  metis_tac[run_named_fn_schedules_data_bytes_section]
QED

Theorem run_callee_first_data_bytes_section:
  run_callee_first rpolicy passes names unit supply = SOME (unit',supply') /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  simp[run_callee_first_def] >>
  metis_tac[run_named_fn_schedules_data_bytes_section]
QED

Theorem run_pipeline_stage_data_bytes_section:
  run_pipeline_stage rpolicy stage unit supply = SOME (unit',supply') /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  Cases_on `stage` >> simp[run_pipeline_stage_def] >>
  metis_tac[run_mapped_functions_data_bytes_section]
QED

Theorem run_pipeline_stages_data_bytes_section:
  !stages unit supply unit' supply'.
  run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') /\
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit.cu_data_segment ==>
  MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
    unit'.cu_data_segment
Proof
  Induct >> simp[run_pipeline_stages_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule run_pipeline_stage_data_bytes_section >>
  disch_then drule >> strip_tac >> first_x_assum irule >>
  metis_tac[]
QED

Theorem run_venom_pipeline_data_bytes_section:
  !mem_ok calling_ok post_ok rpolicy spec unit out label bytes.
    run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out /\
    MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
      unit.cu_data_segment ==>
    MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
      out.po_unit.cu_data_segment
Proof
  simp[run_venom_pipeline_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
     pre_unit.cu_data_segment` by
    metis_tac[run_pipeline_stages_data_bytes_section] >>
  qpat_x_assum `run_callee_first _ _ _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `run_callee_first _ _ _ walk_unit _` >>
  `MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
     walk_unit.cu_data_segment` by
    (simp[Abbr `walk_unit`] >>
     Cases_on `spec.ps_prune_unreachable` >>
     simp[prune_unit_fcg_unreachable_fields]) >>
  strip_tac >> drule run_callee_first_data_bytes_section >>
  disch_then drule >> strip_tac >>
  drule_all run_pipeline_stages_data_bytes_section >> simp[]
QED
