Theory ctorDeployLoweringFrameRunner
Ancestors
  venomFnScheduleRunner venomFnScheduleRunnerProps venomPipelineRunner unitLabelMap cfgTransform
  venomInst list

Theorem subst_label_map_blocks_opcode_every[local]:
  EVERY (\i. P i.inst_opcode)
    (fn_insts_blocks (MAP (subst_label_map_block labels) blocks)) <=>
  EVERY (\i. P i.inst_opcode) (fn_insts_blocks blocks)
Proof
  Induct_on `blocks` >>
  simp[fn_insts_blocks_def, subst_label_map_block_def, subst_label_map_inst_def,
       EVERY_MAP]
QED

Theorem subst_label_map_fn_opcode_every:
  EVERY (\i. P i.inst_opcode) (fn_insts (subst_label_map_fn labels fn)) <=>
  EVERY (\i. P i.inst_opcode) (fn_insts fn)
Proof
  simp[fn_insts_def, subst_label_map_fn_def,
       subst_label_map_blocks_opcode_every]
QED

Theorem filter_subst_label_map_fn_name[local]:
  FILTER (\fn. fn.fn_name = name) (MAP (subst_label_map_fn labels) fns) =
  MAP (subst_label_map_fn labels) (FILTER (\fn. fn.fn_name = name) fns)
Proof
  Induct_on `fns` >> simp[subst_label_map_fn_def] >> gen_tac >>
  Cases_on `h.fn_name = name` >> simp[subst_label_map_fn_def]
QED

Theorem lookup_unique_subst_label_map:
  lookup_unique_function name fns = SOME fn ==>
  lookup_unique_function name (MAP (subst_label_map_fn labels) fns) =
    SOME (subst_label_map_fn labels fn)
Proof
  strip_tac >> drule lookup_unique_function_FILTER >>
  simp[lookup_unique_function_def, filter_subst_label_map_fn_name]
QED

Theorem apply_unit_label_map_opcode_lookup:
  apply_unit_label_map labels u = SOME u' /\
  lookup_unique_function entry u.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
  ?fn'. lookup_unique_function entry u'.cu_context.ctx_functions = SOME fn' /\
        EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  rpt strip_tac >>
  gvs[apply_unit_label_map_def, AllCaseEqs(),
      apply_resolved_unit_label_map_def] >>
  qexists `subst_label_map_fn resolved fn` >>
  simp[lookup_unique_subst_label_map, subst_label_map_fn_opcode_every]
QED

Theorem apply_unit_label_map_function_names:
  apply_unit_label_map labels u = SOME u' ==>
  MAP (\f. f.fn_name) u'.cu_context.ctx_functions =
  MAP (\f. f.fn_name) u.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  gvs[apply_unit_label_map_def, AllCaseEqs(),
      apply_resolved_unit_label_map_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, subst_label_map_fn_def]
QED

Theorem filter_replace_other_name[local]:
  replacement.fn_name = name /\ other <> name ==>
  FILTER (\fn. fn.fn_name = other)
    (MAP (\fn. if fn.fn_name = name then replacement else fn) fns) =
  FILTER (\fn. fn.fn_name = other) fns
Proof
  strip_tac >> Induct_on `fns` >> simp[] >> gen_tac >>
  Cases_on `h.fn_name = name` >> Cases_on `h.fn_name = other` >> gvs[]
QED

Theorem replace_unique_other_lookup:
  replace_unique_function name replacement fns = SOME fns' /\
  lookup_unique_function other fns = SOME fn /\ other <> name ==>
  lookup_unique_function other fns' = SOME fn
Proof
  simp[replace_unique_function_def] >>
  Cases_on `replacement.fn_name = name` >> simp[] >>
  Cases_on `FILTER (\fn. fn.fn_name = name) fns` >> simp[] >>
  Cases_on `t` >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[lookup_unique_function_def, filter_replace_other_name]
QED

Theorem replace_unique_opcode_lookup:
  lookup_unique_function entry fns = SOME fn /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  replace_unique_function name replacement fns = SOME fns' /\
  (name = entry ==> EVERY (\i. P i.inst_opcode) (fn_insts replacement)) ==>
  ?fn'. lookup_unique_function entry fns' = SOME fn' /\
        EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  rpt strip_tac >> Cases_on `name = entry`
  >- (gvs[] >> drule replace_unique_function_exactly_one >> strip_tac >>
      qexists `replacement` >> simp[lookup_unique_function_def]) >>
  `entry <> name` by metis_tac[] >>
  drule_all replace_unique_other_lookup >> strip_tac >>
  qexists `fn` >> simp[]
QED

Theorem configured_fn_pass_fold_opcodes:
  (!pass observed s fn out.
    MEM pass passes /\ runner rp pass observed s fn = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  run_configured_fn_pass_fold runner rp passes unit supply fn labels =
    SOME (fn',labels',supply') ==>
  EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  map_every qid_spec_tac [`supply'`,`labels'`,`fn'`,`labels`,`fn`,`supply`] >>
  Induct_on `passes` >> rpt strip_tac >>
  gvs[run_configured_fn_pass_fold_def, AllCaseEqs()] >>
  first_x_assum irule >> conj_tac
  >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem configured_fn_passes_opcode_lookup:
  (!pass observed s f out.
    MEM pass passes /\ runner rp pass observed s f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  lookup_unique_function entry unit.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  run_configured_fn_passes runner rp passes name unit supply = SOME (unit',supply') ==>
  ?fn'. lookup_unique_function entry unit'.cu_context.ctx_functions = SOME fn' /\
        EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  rpt strip_tac >>
  gvs[run_configured_fn_passes_def, AllCaseEqs()] >>
  irule apply_unit_label_map_opcode_lookup >> goal_assum (drule_at Any) >>
  simp[] >> irule replace_unique_opcode_lookup >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  strip_tac >> gvs[] >>
  irule configured_fn_pass_fold_opcodes >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem named_fn_schedules_opcode_lookup:
  (!pass observed s f out.
    MEM pass passes /\ runner rp pass observed s f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  lookup_unique_function entry unit.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  run_named_fn_schedules runner rp passes names unit supply = SOME (unit',supply') ==>
  ?fn'. lookup_unique_function entry unit'.cu_context.ctx_functions = SOME fn' /\
        EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  map_every qid_spec_tac [`supply'`,`unit'`,`supply`,`unit`,`fn`] >>
  Induct_on `names` >> rpt strip_tac >>
  gvs[run_named_fn_schedules_def, AllCaseEqs()] >>
  drule_all configured_fn_passes_opcode_lookup >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem mapped_functions_opcode_lookup:
  (!observed s f out.
    execute_configured_fn_pass rp pass observed s f = SOME out /\
    EVERY (\i. P i.inst_opcode) (fn_insts f) ==>
    EVERY (\i. P i.inst_opcode) (fn_insts out.fpo_function)) /\
  lookup_unique_function entry unit.cu_context.ctx_functions = SOME fn /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  run_mapped_functions rp pass unit supply = SOME (unit',supply') ==>
  ?fn'. lookup_unique_function entry unit'.cu_context.ctx_functions = SOME fn' /\
        EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  rpt strip_tac >> gvs[run_mapped_functions_def] >>
  irule (INST_TYPE [alpha |-> ``:resolved_compiler_policy``]
    named_fn_schedules_opcode_lookup) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem configured_fn_passes_function_names:
  run_configured_fn_passes runner rp passes name unit supply = SOME (unit',supply') ==>
  MAP (\f. f.fn_name) unit'.cu_context.ctx_functions =
  MAP (\f. f.fn_name) unit.cu_context.ctx_functions
Proof
  rpt strip_tac >> gvs[run_configured_fn_passes_def, AllCaseEqs()] >>
  drule apply_unit_label_map_function_names >> simp[] >>
  drule replace_unique_function_name_order >> simp[]
QED

Theorem named_fn_schedules_function_names:
  run_named_fn_schedules runner rp passes names unit supply = SOME (unit',supply') ==>
  MAP (\f. f.fn_name) unit'.cu_context.ctx_functions =
  MAP (\f. f.fn_name) unit.cu_context.ctx_functions
Proof
  map_every qid_spec_tac [`supply'`,`unit'`,`supply`,`unit`] >>
  Induct_on `names` >> rpt strip_tac >>
  gvs[run_named_fn_schedules_def, AllCaseEqs()] >>
  drule configured_fn_passes_function_names >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem mapped_functions_function_names:
  run_mapped_functions rp pass unit supply = SOME (unit',supply') ==>
  MAP (\f. f.fn_name) unit'.cu_context.ctx_functions =
  MAP (\f. f.fn_name) unit.cu_context.ctx_functions
Proof
  simp[run_mapped_functions_def] >> strip_tac >>
  drule named_fn_schedules_function_names >> simp[]
QED
