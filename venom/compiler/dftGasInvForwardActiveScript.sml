Theory dftGasInvForwardActive
Ancestors
  dftGasInvForwardFunction dftLifting dftWf dftRunRel
  o1PassContract unitShapeDefs contextCodegenRel venomWf venomInst
  venomState venomExecSemantics venomExecProofs list

Theorem inv_target_active_shape:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ dft_fn_rel fn (dft_fn fn) /\
  active_inst (dft_fn fn) inst b ==> inst_shape_ok inst
Proof
  strip_tac >>
  `EVERY inst_shape_ok (fn_insts fn)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum (drule_then assume_tac) >>
     fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM]) >>
  `EVERY inst_shape_ok (fn_insts (dft_fn fn))` by
    (irule dft_fn_inst_shape >> gvs[dft_fn_rel_def]) >>
  gvs[active_inst_def, EVERY_MEM] >> first_x_assum irule >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >> qexists_tac `bb` >> simp[EL_MEM]
QED

Theorem inv_forward_active:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ dft_fn_rel fn (dft_fn fn) /\
  active_inst fn inst a /\ active_inst (dft_fn fn) inst b /\
  a.vs_current_bb = b.vs_current_bb /\ in_revert_forward fn a ==>
  in_revert_forward (dft_fn fn) b
Proof
  strip_tac >>
  `EVERY inst_shape_ok (fn_insts fn)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum (drule_then assume_tac) >>
     fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM]) >>
  `wf_function fn /\ wf_function (dft_fn fn)` by
    (conj_tac >- gvs[dft_fn_rel_def] >>
     irule dft_fn_wf_function >> gvs[dft_fn_rel_def]) >>
  qpat_x_assum `active_inst fn inst a` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  rename1 `MEM src fn.fn_blocks` >>
  `lookup_block a.vs_current_bb fn.fn_blocks = SOME src` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `get_instruction src a.vs_inst_idx = SOME inst` by simp[get_instruction_def] >>
  qpat_x_assum `in_revert_forward fn a` mp_tac >>
  simp[in_revert_forward_def] >> strip_tac >> gvs[] >>
  drule_all inv_forward_fn_at >> strip_tac >>
  qpat_x_assum `active_inst (dft_fn fn) inst b` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  rename1 `MEM target (dft_fn fn).fn_blocks` >>
  `lookup_block b.vs_current_bb (dft_fn fn).fn_blocks = SOME target` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  gvs[] >> rename1 `MEM target (dft_fn fn).fn_blocks` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) target.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `k = b.vs_inst_idx` by
    (gvs[get_instruction_def] >>
     metis_tac[ALL_DISTINCT_EL_IMP, EL_MAP, LENGTH_MAP]) >>
  simp[in_revert_forward_def] >> metis_tac[]
QED
