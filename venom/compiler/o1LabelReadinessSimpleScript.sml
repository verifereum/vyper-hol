Theory o1LabelReadinessSimple
Ancestors
  o1PassContract concretizeStepStructure o1DftStep dftShape dretDesugarProofs
  concretizeMemLocDefs passSharedDefs dftDefs dretDesugarDefs venomPassDispatcher
  unitLabelMapIdentity venomInst

Theorem concretize_inst_label_origin[local]:
  MEM (Label l) (concretize_inst_with_positions p i).inst_operands ==>
  MEM (Label l) i.inst_operands
Proof
  Cases_on `i.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  Cases_on `i.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `FLOOKUP p (Allocation i.inst_id)` >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_label_origin[local]:
  MEM i (fn_insts (concretize_function_with_positions p fn)) /\
  MEM (Label l) i.inst_operands ==>
  ?j. MEM j (fn_insts fn) /\ MEM (Label l) j.inst_operands
Proof
  simp[fn_insts_MEM] >> rpt strip_tac >>
  drule_all concretize_positions_inst_preimage >> strip_tac >> gvs[] >>
  drule concretize_inst_label_origin >> strip_tac >> metis_tac[]
QED

Theorem concretize_context_label_origin[local]:
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM i (fn_insts fn') /\ MEM (Label l) i.inst_operands ==>
  ?j. MEM j (fn_insts fn) /\ MEM (Label l) j.inst_operands
Proof
  rpt strip_tac >>
  gvs[concretize_function_fuel_in_context_def, AllCaseEqs()] >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def,
      fn_insts_def] >>
  metis_tac[concretize_positions_label_origin, fn_insts_def]
QED

Theorem simple_pass_no_runtime_begin:
 !rpolicy tag observed s fn out.
 MEM tag [VP_ConcretizeMemLoc; VP_DFT; VP_DretDesugar] /\
 fn_pass_step rpolicy (CFP_Simple tag) observed s fn out /\
 o1_fn_shape observed.cu_context fn /\
 (!i. MEM i (fn_insts fn) ==> ~MEM (Label "runtime_begin") i.inst_operands) ==>
 !i. MEM i (fn_insts out.fpo_function) ==> ~MEM (Label "runtime_begin") i.inst_operands
Proof
  rpt gen_tac >> simp[] >> strip_tac
  >- (gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
      metis_tac[concretize_context_label_origin])
  >- (gvs[fn_pass_step_def, execute_configured_fn_pass_def] >>
      metis_tac[dft_shape_instruction_source, flip_operands_operand_mem]) >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, o1_fn_shape_def,
      dret_desugar_function_def]
QED
