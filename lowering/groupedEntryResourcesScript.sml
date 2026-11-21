Theory groupedEntryResources
Ancestors
  selectedAcceptedFold moduleLoweringProps allocaFrontierBound
  allocaBudgetProps venomMemDefs ptrDiscipline venomState finite_map arithmetic
  entryValueRevertPtr entryPtrSeamRegister e2eDefs vyperCompiler
  allocaFrontierRoom loweringStateRelDefs venomInst venomWf venomInstIdsProps words
  vyperLoweringCorrect decoderOriginAllocationFrame
  fragGasOriginPtr fragGasPathPtr fragGasPath exprLoweringProps

Theorem grouped_entry_resources_vars_pc:
  selected_registration_resources ctx fn site lo sa s /\
  vars_pc_only s t /\ (s.vs_allocas = FEMPTY \/ sa.cs_next_id <= sb.cs_next_id) /\
  fresh_vars_wrt sb t /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  selected_registration_resources ctx fn site lo sb t
Proof
  strip_tac >>
  fs[vars_pc_only_def, venom_state_component_equality, selected_registration_resources_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, allocas_from_def,
     alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem grouped_entry_frame_vars_pc:
  vars_pc_only s t /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm ==>
  selected_registration_frame s tn t u /\ t.vs_memory = s.vs_memory
Proof
  simp[vars_pc_only_def, venom_state_component_equality, selected_registration_frame_def]
QED
