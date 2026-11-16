Theory o1LabelFlowSourceCfgLabels
Ancestors
  o1ContractSimplifyCfgSrcStatic o1ContractSimplifyCfgStep
  o1ContractSimplifyCfg simplifyCfgStaticInterface simplifyCfgShapeCore
  simplifyCfgDefs cfgTransform simplifyCfgPhiProps simplifyCfgCorrectness codegenAsmStaticWf
  o1PassContract unitShapeDefs venomWf venomInst list pred_set

Theorem shaped_terminator_label_is_jump:
  !i l. label_positions_ok i /\ is_terminator i.inst_opcode /\
    MEM (Label l) i.inst_operands ==> MEM i.inst_opcode [JMP; JNZ]
Proof
  rpt gen_tac >> Cases_on `i.inst_opcode` >>
  simp[is_terminator_def, label_positions_ok_def] >>
  rpt strip_tac >> gvs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem simplify_cfg_fn_no_reserved_operand:
  !C f l.
    o1_fn_shape C f /\ fn_defs_reach_uses f /\ reserved_label l /\
    EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) /\
    (!i. MEM i (fn_insts f) ==> ~MEM (Label l) i.inst_operands) ==>
    !i. MEM i (fn_insts (simplify_cfg_fn f)) ==>
      ~MEM (Label l) i.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  `simplify_cfg_fn_ok f` by
    (irule simplify_cfg_fn_ok_no_phi >> gvs[o1_fn_shape_def]) >>
  `scfg_static f` by
    (simp[scfg_static_def] >>
     metis_tac[o1_fn_shape_def, fn_shape_ok_scfg_shape]) >>
  `EVERY no_phis f.fn_blocks` by
    (gvs[no_phis_def, EVERY_MEM, fn_insts_def,
         MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  drule_all simplify_cfg_fn_data_insts >>
  simp[EXTENSION, MEM_FILTER] >> strip_tac >>
  `o1_fn_shape C (simplify_cfg_fn f)` by
    (simp[simplify_cfg_fn_def] >> irule simplify_cfg_o1_fn_shape >> simp[]) >>
  gen_tac >> strip_tac >>
  Cases_on `is_terminator i.inst_opcode`
  >- (strip_tac >>
      `label_positions_ok i` by
        (gvs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
             inst_shape_ok_def] >> metis_tac[]) >>
      drule_all shaped_terminator_label_is_jump >> strip_tac >>
      `?bb. MEM bb (simplify_cfg_fn f).fn_blocks /\
             MEM i bb.bb_instructions` by
        metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff] >>
      `bb_well_formed bb` by metis_tac[o1_fn_shape_def, wf_function_def] >>
      drule_all block_jump_ref_successor >> strip_tac >>
      `MEM l (fn_labels (simplify_cfg_fn f))` by
        metis_tac[o1_fn_shape_def, wf_function_def, fn_succs_closed_def] >>
      gvs[o1_fn_shape_def, fn_shape_ok_def, fn_labels_def, MEM_MAP,
          EVERY_MEM] >> metis_tac[]) >>
  `MEM i (fn_insts (reachable_fn f))` by metis_tac[] >>
  strip_tac >> drule_all reachable_fn_insts_operand >> metis_tac[]
QED
