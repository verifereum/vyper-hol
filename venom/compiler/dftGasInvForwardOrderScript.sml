Theory dftGasInvForwardOrder
Ancestors
  dftDefs contextCodegenRel cfgHelpers venomWf list unitShapeDefs
  stackPlanTypes o1PassContract venomInst venomState rich_list

Definition inv_order_label_bb_def:
  inv_order_label_bb = <|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 RETURNDATACOPY [Label "entry"; Lit 0w; Lit 8w] [];
     mk_inst 1 REVERT [Label "entry"; Lit 8w] []]|>
End

Theorem inv_order_wf_not_enough:
  wf_function (mk_raw_function "f" [inv_order_label_bb]) /\
  revert_forward_pair inv_order_label_bb 0 1 /\
  cfg_succs_of (cfg_analyze (mk_raw_function "f" [inv_order_label_bb]))
    inv_order_label_bb.bb_label = ["entry"]
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> decide_tac
QED

Theorem inv_order_revert_successors:
  inst.inst_opcode = REVERT /\ label_positions_ok inst ==>
  get_successors inst = []
Proof
  strip_tac >>
  gvs[label_positions_ok_def, get_successors_def, is_terminator_def] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  qspec_tac (`inst.inst_operands`, `ops`) >> Induct >> simp[] >>
  qx_gen_tac `op` >>
  Cases_on `op` >> simp[is_label_operand_def, get_label_def]
QED

Theorem inv_order_forward_block_successors:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_shape_ok bb.bb_instructions /\ revert_forward_pair bb i j ==>
  cfg_succs_of (cfg_analyze fn) bb.bb_label = []
Proof
  strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  `j = PRE (LENGTH bb.bb_instructions)` by
    (gvs[bb_well_formed_def] >>
     first_x_assum irule >> simp[is_terminator_def]) >>
  `(LAST bb.bb_instructions).inst_opcode = REVERT` by
    (gvs[bb_well_formed_def, LAST_EL]) >>
  `get_successors (LAST bb.bb_instructions) = []` by
    (irule inv_order_revert_successors >>
     gvs[EVERY_MEM, inst_shape_ok_def] >>
     metis_tac[MEM_LAST_NOT_NIL, bb_well_formed_def]) >>
  simp[cfg_analyze_succs] >>
  `fmap_lookup_list (build_succs fn.fn_blocks) bb.bb_label = bb_succs bb` by
    (irule cfg_succs_of_build_succs >> gvs[wf_function_def, fn_labels_def]) >>
  simp[] >> Cases_on `bb.bb_instructions` >> gvs[bb_succs_def]
QED

Theorem inv_order_forward_source_successors:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j ==>
  cfg_succs_of (cfg_analyze fn) bb.bb_label = []
Proof
  strip_tac >> irule inv_order_forward_block_successors >>
  simp[] >>
  `wf_function fn /\ EVERY inst_shape_ok (fn_insts fn)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_shape_ok_def] >>
     metis_tac[]) >>
  simp[] >> gvs[EVERY_MEM, fn_insts_def] >>
  metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks]
QED

Theorem inv_order_forward_source_stack:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j ==>
  so_get_stack (cfg_analyze fn) lr current_fn ft bb.bb_label = ([],ft)
Proof
  strip_tac >> drule_all inv_order_forward_source_successors >>
  simp[stackOrderDefsTheory.so_get_stack_def,
       stackOrderInternalDefsTheory.so_merge_def]
QED

Theorem inv_order_forward_process_blocks:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  lookup_block bb.bb_label st.dls_blocks = SOME current_bb /\
  dft_process_one (cfg_analyze fn) lr fn st bb.bb_label = (st',converged,out_labels) ==>
  st'.dls_blocks = st.dls_blocks \/
  st'.dls_blocks = MAP (\b. if b.bb_label = bb.bb_label then
    dft_block [] current_bb else b) st.dls_blocks
Proof
  strip_tac >>
  `!lr cur ft. so_get_stack (cfg_analyze fn) lr cur ft bb.bb_label = ([],ft)` by
    (rpt gen_tac >> irule inv_order_forward_source_stack >> metis_tac[]) >>
  qpat_x_assum `dft_process_one _ _ _ _ _ = _` mp_tac >>
  simp[dft_process_one_def] >> pairarg_tac >> simp[] >>
  Cases_on `FLOOKUP st.dls_last_order bb.bb_label` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED
