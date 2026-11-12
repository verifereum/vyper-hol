Theory concretizeStepShape
Ancestors
  concretizeStepRetpc concretizeStepStructure
  concretizeMemLocDefs unitShapeDefs venomInst venomWf passSharedDefs
  o1PassContract irSupply list stackPlanTypes passSimulationDefs dretDesugarDefs
  passTransform

Theorem concretize_positions_every:
  EVERY P (fn_insts fn) /\
  (!i. P i ==> P (concretize_inst_with_positions p i)) ==>
  EVERY P (fn_insts (concretize_function_with_positions p fn))
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem concretize_positions_inst_shape:
  inst_shape_ok i ==> inst_shape_ok (concretize_inst_with_positions p i)
Proof
  Cases_on `i.inst_opcode = ALLOCA`
  >- (simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
      simp[mk_assign_inst_def, mk_nop_inst_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, is_label_operand_def]) >>
  simp[concretize_positions_unchanged]
QED

Theorem concretize_positions_fn_name[simp]:
  (concretize_function_with_positions p fn).fn_name = fn.fn_name
Proof
  simp[concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def]
QED

Theorem concretize_positions_fn_shape:
  wf_function fn /\ fn_shape_ok fn ==>
  fn_shape_ok (concretize_function_with_positions p fn)
Proof
  strip_tac >> fs[fn_shape_ok_def] >>
  simp[fn_shape_ok_def, concretize_positions_entry_label,
       concretize_positions_opaque_use, concretize_positions_retpc_shape] >> conj_tac
  >- simp[concretize_positions_blocks, EVERY_MAP,
          concretize_positions_block_label] >>
  irule concretize_positions_every >> simp[concretize_positions_inst_shape]
QED

Theorem concretize_positions_first_block:
  wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn ==>
  first_block_no_preds (concretize_function_with_positions p fn) /\
  first_block_no_phi (concretize_function_with_positions p fn)
Proof
  strip_tac >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  `!bb. MEM bb fn.fn_blocks ==>
     bb_succs (clear_nops_block
       (block_map_transform (concretize_inst_with_positions p) bb)) = bb_succs bb` by
    (rpt strip_tac >> irule concretize_positions_block_succs >>
     fs[wf_function_def]) >>
  conj_tac
  >- (Cases_on `fn.fn_blocks` >> gvs[] >>
      simp[first_block_no_preds_def, concretize_positions_blocks,
           concretize_positions_block_label, EVERY_MAP, EVERY_MEM] >>
      rpt strip_tac >> gvs[MEM_MAP] >>
      fs[first_block_no_preds_def, EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
      metis_tac[]) >>
  Cases_on `fn.fn_blocks` >> gvs[] >>
  simp[first_block_no_phi_def, concretize_positions_blocks,
       clear_nops_block_def, block_map_transform_def, EVERY_FILTER, EVERY_MAP] >>
  fs[first_block_no_phi_def, EVERY_MEM] >>
  metis_tac[concretize_positions_phi]
QED

Theorem concretize_positions_other_opcode:
  ~MEM (concretize_inst_with_positions p i).inst_opcode [ASSIGN; NOP] ==>
  concretize_inst_with_positions p i = i
Proof
  simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_invoke_ok:
  fn_invoke_ok names fn ==>
  fn_invoke_ok names (concretize_function_with_positions p fn)
Proof
  simp[fn_invoke_ok_def] >> rpt strip_tac >>
  drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  `concretize_inst_with_positions p oldi = oldi` by
    (irule concretize_positions_other_opcode >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem concretize_positions_label_refs:
  fn_label_refs_ok fn ==>
  fn_label_refs_ok (concretize_function_with_positions p fn)
Proof
  simp[fn_label_refs_ok_def, concretize_positions_labels] >> rpt strip_tac >>
  drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  `concretize_inst_with_positions p oldi = oldi` by
    (qpat_x_assum `MEM (Label _) _` mp_tac >>
     simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
     simp[mk_assign_inst_def, mk_nop_inst_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem concretize_positions_dalloca:
  (!i x. MEM i (fn_insts fn) /\ i.inst_opcode = DALLOCA /\ MEM x i.inst_outputs ==>
     ~gas_var fn x /\ ~retpc_var fn x) ==>
  (!i x. MEM i (fn_insts (concretize_function_with_positions p fn)) /\
     i.inst_opcode = DALLOCA /\ MEM x i.inst_outputs ==>
     ~gas_var (concretize_function_with_positions p fn) x /\
     ~retpc_var (concretize_function_with_positions p fn) x)
Proof
  rpt strip_tac >> drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  `concretize_inst_with_positions p oldi = oldi` by
    (irule concretize_positions_other_opcode >> simp[]) >>
  gvs[gas_var_def, retpc_var_def, concretize_positions_copy_phi] >> metis_tac[]
QED

Theorem concretize_positions_opcode_every:
  EVERY (\i. P i.inst_opcode) (fn_insts fn) /\ P ASSIGN /\ P NOP ==>
  EVERY (\i. P i.inst_opcode) (fn_insts (concretize_function_with_positions p fn))
Proof
  strip_tac >> irule concretize_positions_every >> simp[] >>
  rpt strip_tac >> simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_o1_fn_shape:
  o1_fn_shape ctx fn ==> o1_fn_shape ctx (concretize_function_with_positions p fn)
Proof
  strip_tac >> fs[o1_fn_shape_def] >>
  drule_all concretize_positions_first_block >> strip_tac >>
  drule concretize_positions_dalloca >> strip_tac >>
  simp[o1_fn_shape_def, concretize_positions_preserves_wf,
       concretize_positions_fn_inst_wf, concretize_positions_fn_shape,
       concretize_positions_invoke_ok, concretize_positions_label_refs,
       concretize_positions_dalloca] >>
  rpt conj_tac
  >- (`EVERY (\i. i.inst_opcode <> DRET)
          (fn_insts (concretize_function_with_positions p fn))` by
        (ho_match_mp_tac concretize_positions_opcode_every >> fs[no_dret_def, EVERY_MEM]) >>
      fs[no_dret_def, EVERY_MEM])
  >- metis_tac[]
  >- (strip_tac >> fs[entry_fn_no_return_def, entry_fn_no_params_def] >>
      conj_tac >> ho_match_mp_tac concretize_positions_opcode_every >> simp[is_param_opcode_def]) >>
  strip_tac >> ho_match_mp_tac concretize_positions_opcode_every >> simp[]
QED

Theorem concretize_positions_fresh_names:
  fresh_names_ok s fn (concretize_function_with_positions p fn)
Proof
  simp[fresh_names_ok_def, concretize_positions_labels,
       fn_ir_inst_ids_def, block_ir_inst_ids_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >>
  rpt strip_tac >> disj1_tac >>
  drule_all concretize_positions_inst_preimage >> strip_tac >>
  gvs[concretize_positions_inst_id] >> metis_tac[]
QED
