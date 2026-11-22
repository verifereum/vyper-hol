(* Preservation and assembly of the runtime bytes appended to a deploy unit. *)
Theory deployRuntimeSuffix
Ancestors
  venomPipelineData venomPipelineDriver venomPipelineRunner venomFnScheduleRunner
  unitLabelMap fcgPruning ctorDeployInitcodeAsm codegenEncodingWf
  asmWf asmIR symbolResolve
  finite_map list rich_list

Theorem deploy_label_map_runtime_suffix[local]:
  apply_unit_label_map lm unit = SOME unit' /\
  unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>] ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[apply_unit_label_map_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[apply_resolved_unit_label_map_def] >>
  simp[MAP_APPEND] >> metis_tac[]
QED

Theorem deploy_fn_pass_runtime_suffix[local]:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[run_configured_fn_passes_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule deploy_label_map_runtime_suffix >> simp[]
QED

Theorem deploy_named_pass_runtime_suffix[local]:
  !names unit supply unit' supply'.
  run_named_fn_schedules runner rpolicy passes names unit supply =
    SOME (unit',supply') /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  Induct >> simp[run_named_fn_schedules_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule deploy_fn_pass_runtime_suffix >>
  disch_then (qspec_then `bytes` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem deploy_mapped_runtime_suffix[local]:
  run_mapped_functions rpolicy pass unit supply = SOME (unit',supply') /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[run_mapped_functions_def] >>
  metis_tac[deploy_named_pass_runtime_suffix]
QED

Theorem deploy_callee_runtime_suffix[local]:
  run_callee_first rpolicy passes names unit supply = SOME (unit',supply') /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[run_callee_first_def] >>
  metis_tac[deploy_named_pass_runtime_suffix]
QED

Theorem deploy_stage_runtime_suffix[local]:
  run_pipeline_stage rpolicy stage unit supply = SOME (unit',supply') /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  Cases_on `stage` >> simp[run_pipeline_stage_def] >>
  metis_tac[deploy_mapped_runtime_suffix]
QED

Theorem deploy_stages_runtime_suffix[local]:
  !stages unit supply unit' supply'.
  run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. unit'.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  Induct >> simp[run_pipeline_stages_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule deploy_stage_runtime_suffix >>
  disch_then (qspec_then `bytes` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem deploy_pipeline_runtime_suffix:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out /\
  (?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]) ==>
  ?pre'. out.po_unit.cu_data_segment = pre' ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[run_venom_pipeline_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `?pre. pre_unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]` by
    metis_tac[deploy_stages_runtime_suffix] >>
  qpat_x_assum `run_callee_first _ _ _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `run_callee_first _ _ _ walk_unit _` >>
  `?pre. walk_unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]` by
    (simp[Abbr `walk_unit`] >> Cases_on `spec.ps_prune_unreachable` >>
     simp[fcgPruningTheory.prune_unit_fcg_unreachable_fields] >> metis_tac[]) >>
  strip_tac >> drule deploy_callee_runtime_suffix >>
  disch_then (qspec_then `bytes` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[deploy_stages_runtime_suffix]
QED

Theorem deploy_runtime_suffix_offset:
  FLOOKUP (SND (compute_label_offsets
    (pre ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
             AsmDataHeader "code_end"]))) "runtime_begin" =
    SOME (SUM (MAP asm_inst_size pre))
Proof
  simp[compute_label_offsets_def, FOLDL_APPEND] >>
  Cases_on `compute_label_offsets pre` >>
  gvs[compute_label_offsets_def] >>
  simp[symbolResolveTheory.asm_inst_size_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  mp_tac (Q.SPEC `pre` compute_label_offsets_bound) >>
  simp[compute_label_offsets_def]
QED

Theorem deploy_runtime_suffix_slice:
  asm_encoding_wf (pre ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
                         AsmDataHeader "code_end"]) ==>
  DROP (SUM (MAP asm_inst_size pre))
    (assemble (pre ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
                      AsmDataHeader "code_end"])) = bytes
Proof
  strip_tac >> drule deploy_encoding_total_length >>
  Cases_on `compute_label_offsets
    (pre ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes;
             AsmDataHeader "code_end"])` >>
  simp[assemble_def, MAP_APPEND, FLAT_APPEND, encode_inst_def,
       symbolResolveTheory.asm_inst_size_def, SUM_APPEND] >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `DROP _ (prefix ++ bytes)` >>
  `LENGTH prefix = SUM (MAP asm_inst_size pre)` by
    gvs[Abbr `prefix`] >>
  metis_tac[DROP_LENGTH_APPEND]
QED
