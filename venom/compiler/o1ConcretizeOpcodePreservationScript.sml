Theory o1ConcretizeOpcodePreservation
Ancestors
  concretizeMemLocDefs concretizeStageShape passSharedDefs passTransform
  venomInst ctxLookupAgreeHelpers list

Theorem concretize_inst_no_returndatacopy[local]:
  inst.inst_opcode <> RETURNDATACOPY ==>
  (concretize_inst_with_positions positions inst).inst_opcode <> RETURNDATACOPY
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA` >>
  gvs[concretize_inst_with_positions_def] >>
  namedCases_on `inst.inst_outputs` ["", "out rest"] >> gvs[] >>
  Cases_on `rest` >> gvs[] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_no_returndatacopy[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY)
    (fn_insts (concretize_function_with_positions positions fn))
Proof
  rewrite_tac[concretize_function_with_positions_def,
              clear_nops_function_def, function_map_transform_def] >>
  simp[fn_insts_def] >>
  rewrite_tac[fn_insts_EVERY_block, EVERY_MAP, EVERY_MEM] >>
  BETA_TAC >> rpt strip_tac >>
  gvs[concretize_positions_block_instruction] >>
  metis_tac[concretize_inst_no_returndatacopy]
QED

Theorem concretize_function_fuel_in_context_no_returndatacopy:
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY) (fn_insts fn')
Proof
  simp[concretize_function_fuel_in_context_def] >>
  Cases_on `fn_has_static_layout fn` >> simp[]
  >- (rpt strip_tac >> gvs[AllCaseEqs()]) >>
  Cases_on `if fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []
            then compute_function_layout_fuel_in_context fuel ctx reserved fn
            else compute_function_layout_eval reserved fn` >> simp[] >>
  strip_tac >> gvs[] >>
  drule concretize_positions_no_returndatacopy >>
  simp[apply_context_concretize_layout_def, apply_concretize_layout_def,
       fn_insts_def]
QED
