(* Conditional opcode interfaces for the checked pipeline runners. *)
Theory o1OpcodeRunnerPreservation
Ancestors
  venomPipelineRunnerProps venomPipelineRunner venomFnScheduleRunnerProps
  venomFnScheduleRunner venomPassDispatcher venomPassSchedule unitLabelMap
  cfgTransform venomInst venomWf list o1ScheduleDecompHelpers

Theorem subst_label_map_fn_opcode_every[local]:
  EVERY (\i. P i.inst_opcode) (fn_insts (subst_label_map_fn labels fn)) <=>
  EVERY (\i. P i.inst_opcode) (fn_insts fn)
Proof
  simp[fn_insts_def, subst_label_map_fn_def,
       subst_label_map_blocks_opcode_every]
QED

Theorem run_configured_fn_pass_fold_opcode_every[local]:
  !passes s fn labels fn' labels' s'.
  (!pass u supply f out.
    MEM pass passes /\ runner rpolicy pass u supply f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  run_configured_fn_pass_fold runner rpolicy passes unit s fn labels =
    SOME (fn',labels',s') /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
  EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  Induct_on `passes`
  >- simp[run_configured_fn_pass_fold_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[run_configured_fn_pass_fold_def, AllCaseEqs()] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem apply_unit_label_map_selected_opcodes[local]:
  apply_unit_label_map labels unit = SOME unit' /\
  (!f. MEM f unit.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)) ==>
  (!f. MEM f unit'.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f))
Proof
  simp[apply_unit_label_map_def, AllCaseEqs()] >> strip_tac >>
  gvs[apply_resolved_unit_label_map_def, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  gvs[subst_label_map_fn_opcode_every, subst_label_map_fn_def] >>
  metis_tac[]
QED

Theorem run_configured_fn_passes_selected_opcodes[local]:
  (!pass u supply f out.
    MEM pass passes /\ execute_configured_fn_pass rpolicy pass u supply f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  run_configured_fn_passes execute_configured_fn_pass rpolicy passes name unit s =
    SOME (unit',s') /\
  (!f. MEM f unit.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)) ==>
  (!f. MEM f unit'.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[run_configured_fn_passes_def, AllCaseEqs()] >>
  drule apply_unit_label_map_selected_opcodes >>
  disch_then (qspecl_then [`selected`,`P`] assume_tac) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  gvs[replace_unique_function_def, AllCaseEqs(), MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  drule lookup_unique_function_member >> strip_tac >>
  drule run_configured_fn_pass_fold_opcode_every >>
  metis_tac[]
QED

Theorem run_named_fn_schedules_selected_opcodes[local]:
  !names unit s unit' s'.
  (!pass u supply f out.
    MEM pass passes /\ execute_configured_fn_pass rpolicy pass u supply f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  run_named_fn_schedules execute_configured_fn_pass rpolicy passes names unit s =
    SOME (unit',s') /\
  (!f. MEM f unit.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)) ==>
  (!f. MEM f unit'.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f))
Proof
  Induct_on `names`
  >- simp[run_named_fn_schedules_def] >>
  rpt gen_tac >> strip_tac >>
  drule run_named_fn_schedules_cons_success >> strip_tac >>
  `!f. MEM f unit1.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)` by
    (drule run_configured_fn_passes_selected_opcodes >>
     metis_tac[]) >>
  qpat_x_assum `!unit s unit' s'. _`
    (qspecl_then [`unit1`,`supply1`,`unit'`,`s'`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[MEM]) >> simp[]
QED

Theorem run_callee_first_opcode_every:
  (!pass u supply f out.
    MEM pass passes /\ execute_configured_fn_pass rpolicy pass u supply f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  run_callee_first rpolicy passes names unit s = SOME (unit',s') /\
  (!f. MEM f unit.cu_context.ctx_functions ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)) ==>
  (!f. MEM f unit'.cu_context.ctx_functions ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f))
Proof
  strip_tac >> gvs[run_callee_first_def] >>
  drule run_named_fn_schedules_selected_opcodes >>
  disch_then (qspec_then `\name. T` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem run_pipeline_stages_selected_opcodes:
  !stages unit s unit' s'.
  (!pass u supply f out.
    MEM (PS_MapFunctions pass) stages /\
    execute_configured_fn_pass rpolicy pass u supply f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  run_pipeline_stages rpolicy stages unit s = SOME (unit',s') /\
  (!f. MEM f unit.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)) ==>
  (!f. MEM f unit'.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f))
Proof
  Induct_on `stages`
  >- simp[run_pipeline_stages_def] >>
  rpt gen_tac >> strip_tac >>
  drule run_pipeline_stages_cons_success >> strip_tac >>
  `!f. MEM f unit1.cu_context.ctx_functions /\ selected f.fn_name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)` by
    (Cases_on `h` >>
     gvs[run_pipeline_stage_def, run_mapped_functions_def] >>
     drule_at Any run_named_fn_schedules_selected_opcodes >>
     disch_then (qspecl_then [`selected`,`P`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `!unit s unit' s'. _`
    (qspecl_then [`unit1`,`supply1`,`unit'`,`s'`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[MEM]) >> simp[]
QED

Theorem run_configured_fn_passes_entry[local]:
  run_configured_fn_passes runner rpolicy passes name unit s = SOME (unit',s') ==>
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry
Proof
  simp[run_configured_fn_passes_def, AllCaseEqs()] >> strip_tac >>
  gvs[apply_unit_label_map_def, AllCaseEqs(),
      apply_resolved_unit_label_map_def]
QED

Theorem run_named_fn_schedules_entry[local]:
  !names unit s unit' s'.
  run_named_fn_schedules runner rpolicy passes names unit s = SOME (unit',s') ==>
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry
Proof
  Induct_on `names`
  >- simp[run_named_fn_schedules_def] >>
  rpt strip_tac >> drule run_named_fn_schedules_cons_success >> strip_tac >>
  drule run_configured_fn_passes_entry >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem run_pipeline_stages_entry:
  !stages unit s unit' s'.
  run_pipeline_stages rpolicy stages unit s = SOME (unit',s') ==>
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry
Proof
  Induct_on `stages`
  >- simp[run_pipeline_stages_def] >>
  rpt strip_tac >> drule run_pipeline_stages_cons_success >> strip_tac >>
  `unit1.cu_context.ctx_entry = unit.cu_context.ctx_entry` by
    (Cases_on `h` >>
     gvs[run_pipeline_stage_def, run_mapped_functions_def] >>
     metis_tac[run_named_fn_schedules_entry]) >>
  first_x_assum drule >> simp[]
QED

Theorem run_pipeline_stages_ctx_wf:
  run_pipeline_stages rpolicy stages unit s = SOME (unit',s') /\
  ctx_wf unit.cu_context ==> ctx_wf unit'.cu_context
Proof
  strip_tac >>
  drule run_pipeline_stages_structural >> strip_tac >>
  drule run_pipeline_stages_entry >> strip_tac >>
  gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_has_entry_def]
QED

Theorem run_pipeline_stages_lookup_opcodes:
  (!pass u supply f out.
    MEM (PS_MapFunctions pass) stages /\
    execute_configured_fn_pass rpolicy pass u supply f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  run_pipeline_stages rpolicy stages unit s = SOME (unit',s') /\
  ctx_wf unit.cu_context /\
  lookup_function name unit.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
  ?fn'. lookup_function name unit'.cu_context.ctx_functions = SOME fn' /\
        EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions)` by
    fs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  `!f. MEM f unit.cu_context.ctx_functions /\ f.fn_name = name ==>
       EVERY (\i. P i.inst_opcode) (fn_insts f)` by
    (rpt strip_tac >>
     `lookup_function name unit.cu_context.ctx_functions = SOME f` by
       simp[lookup_function_member_iff] >> gvs[]) >>
  drule_at Any run_pipeline_stages_selected_opcodes >>
  disch_then (qspecl_then [`\n. n = name`,`P`] mp_tac) >>
  simp[] >> strip_tac >>
  drule run_pipeline_stages_structural >> strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) unit'.cu_context.ctx_functions)` by
    gvs[ctx_fn_names_def] >>
  `MEM name (ctx_fn_names unit'.cu_context)` by
    (gvs[ctx_fn_names_def] >>
     drule lookup_function_member_iff >> strip_tac >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `ctx_fn_names unit'.cu_context = _` kall_tac >>
  qpat_x_assum `MEM name (ctx_fn_names unit'.cu_context)` mp_tac >>
  simp[ctx_fn_names_def, MEM_MAP] >>
  disch_then (qx_choose_then `found` strip_assume_tac) >>
  qexists `found` >> simp[lookup_function_member_iff] >>
  qpat_x_assum `!f'. _` irule >> simp[] >> gvs[]
QED
