(* Dispatcher and original-input interfaces for the FMP step contract. *)
Theory fmpStepBridge
Ancestors
  fmpStepShape venomFnScheduleRunnerProps venomFnScheduleRunner
  venomPassDispatcher o1PassContract irSupply list

Theorem ir_supply_covers_unit_member:
  ir_supply_covers_unit s unit /\ MEM fn unit.cu_context.ctx_functions ==>
  ir_supply_covers_fn s fn
Proof
  simp[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
    unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
    EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem fmp_fn_pass_step_result:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s fn out ==>
  fmp_lower_function observed.cu_context s fn =
    SOME (out.fpo_function,out.fpo_supply) /\ out.fpo_label_map = []
Proof
  simp[fn_pass_step_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_fn_pass_step_input:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s fn out /\
  o1_ctx_shape observed.cu_context ==>
  o1_fn_shape observed.cu_context fn /\ ir_supply_covers_fn s fn
Proof
  strip_tac >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >> drule lookup_unique_function_member >> simp[]) >>
  conj_tac >- gvs[o1_ctx_shape_def, EVERY_MEM] >>
  irule ir_supply_covers_unit_member >> qexists `observed` >>
  gvs[fn_pass_step_def]
QED
