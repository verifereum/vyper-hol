Theory o1SymStaticSimple
Ancestors
  o1DftStep o1ContractSueStep singleUseExpansionSupplySim dftShape
  lowerDloadDefs concretizeMemLocDefs dretDesugarDefs venomInst
  passSharedDefs passSharedProps passTransform unitLabelMapIdentity list

Theorem dft_runtime_reflect:
  o1_fn_shape ctx fn /\
  (?i. MEM i (fn_insts (dft_fn fn)) /\
       MEM (Label "runtime_begin") i.inst_operands) ==>
  ?i. MEM i (fn_insts fn) /\
      MEM (Label "runtime_begin") i.inst_operands
Proof
  strip_tac >> drule_all dft_shape_instruction_source >>
  strip_tac >> gvs[flip_operands_operand_mem] >> metis_tac[]
QED

Theorem dret_runtime_reflect:
  no_dret fn /\ dret_desugar_function target s fn = SOME (fn',s') /\
  (?i. MEM i (fn_insts fn') /\
       MEM (Label "runtime_begin") i.inst_operands) ==>
  ?i. MEM i (fn_insts fn) /\
      MEM (Label "runtime_begin") i.inst_operands
Proof
  strip_tac >> gvs[dret_desugar_function_def] >> metis_tac[]
QED

Theorem sue_runtime_reflect:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') /\
  (?j. MEM j (fn_insts fn') /\
       MEM (Label "runtime_begin") j.inst_operands) ==>
  ?i. MEM i (fn_insts fn) /\
      MEM (Label "runtime_begin") i.inst_operands
Proof
  strip_tac >> drule_all sue_expand_function_supply_label_projection >>
  strip_tac
  >- gvs[venomStateTheory.get_label_def] >>
  drule sue_label_projection_mem >> metis_tac[]
QED

Theorem lower_dload_inst_runtime_reflect:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  MEM (Label "runtime_begin") j.inst_operands ==>
  MEM (Label "runtime_begin") i.inst_operands
Proof
  rw[lower_dload_inst_supply_def, AllCaseEqs()] >> gvs[]
QED

Theorem lower_dload_insts_runtime_reflect:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\
  MEM j xs /\ MEM (Label "runtime_begin") j.inst_operands ==>
  ?i. MEM i ins /\ MEM (Label "runtime_begin") i.inst_operands
Proof
  Induct_on `ins` >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs(), MEM_APPEND] >>
  metis_tac[lower_dload_inst_runtime_reflect]
QED

Theorem lower_dload_blocks_runtime_reflect:
  !s bs t. lower_dload_blocks_supply s blocks = (bs,t) /\
  MEM b bs /\ MEM j b.bb_instructions /\
  MEM (Label "runtime_begin") j.inst_operands ==>
  ?a i. MEM a blocks /\ MEM i a.bb_instructions /\
        MEM (Label "runtime_begin") i.inst_operands
Proof
  Induct_on `blocks` >> simp[lower_dload_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), lower_dload_block_supply_def] >>
  metis_tac[lower_dload_insts_runtime_reflect]
QED

Theorem lower_dload_runtime_reflect:
  lower_dload_function_supply s fn = (fn',s') /\
  (?i. MEM i (fn_insts fn') /\
       MEM (Label "runtime_begin") i.inst_operands) ==>
  ?i. MEM i (fn_insts fn) /\
      MEM (Label "runtime_begin") i.inst_operands
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_MEM] >>
  strip_tac >> gvs[] >> drule_all lower_dload_blocks_runtime_reflect >>
  metis_tac[]
QED

Theorem concretize_inst_label_reflect:
  MEM (Label l) (concretize_inst_with_positions p i).inst_operands ==>
  MEM (Label l) i.inst_operands
Proof
  rw[concretize_inst_with_positions_def, AllCaseEqs(),
     mk_assign_inst_def, mk_nop_inst_def] >>
  Cases_on `i.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `FLOOKUP p (Allocation i.inst_id)` >> gvs[]
QED

Theorem concretize_positions_runtime_reflect:
  (?i. MEM i (fn_insts (concretize_function_with_positions p fn)) /\
       MEM (Label "runtime_begin") i.inst_operands) ==>
  ?i. MEM i (fn_insts fn) /\
      MEM (Label "runtime_begin") i.inst_operands
Proof
  strip_tac >> fs[concretize_function_with_positions_def] >>
  drule clear_nops_fn_insts_subset >>
  simp[fn_insts_MEM, function_map_transform_def, block_map_transform_def,
       MEM_MAP] >> strip_tac >> gvs[MEM_MAP] >>
  drule concretize_inst_label_reflect >> metis_tac[]
QED

Theorem concretize_context_runtime_reflect:
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  (?i. MEM i (fn_insts fn') /\
       MEM (Label "runtime_begin") i.inst_operands) ==>
  ?i. MEM i (fn_insts fn) /\
      MEM (Label "runtime_begin") i.inst_operands
Proof
  simp[concretize_function_fuel_in_context_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  >- metis_tac[] >>
  fs[apply_context_concretize_layout_def, apply_concretize_layout_def,
     fn_insts_def] >>
  irule (SRULE [fn_insts_def] concretize_positions_runtime_reflect) >>
  qexists_tac `layout.cl_positions` >> metis_tac[]
QED
