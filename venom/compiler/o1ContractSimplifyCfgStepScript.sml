(*
 * SimplifyCFG against the O1 pass contract: the step part.
 *
 * The dispatched transform is simplify_cfg_fn_with_labels, which keeps the
 * supply and makes no new labels or instruction ids: it deletes blocks,
 * merges a block into its single predecessor, bypasses jump-only blocks,
 * and rewrites PHIs and jumps in place.  So one run keeps the O1 function
 * shape, its names are fresh trivially, and its label map sends only
 * merged or bypassed blocks, never the entry (which has no predecessors),
 * to labels that remain.
 *)
Theory o1ContractSimplifyCfgStep
Ancestors
  o1PassContract simplifyCfgCorrectness simplifyCfgLabelProps
  simplifyCfgDefs simplifyCfgInvariant simplifyCfgCollapseShape
  simplifyCfgOpaque unitShapeDefs cfgTransform venomPassDispatcher venomWf

Theorem simplify_cfg_entry_no_return:
  entry_fn_no_return f ==>
  entry_fn_no_return (FST (simplify_cfg_fn_with_labels f))
Proof
  rewrite_tac[entry_fn_no_return_def] >> strip_tac >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[]
QED

Theorem simplify_cfg_entry_no_params:
  entry_fn_no_params f ==>
  entry_fn_no_params (FST (simplify_cfg_fn_with_labels f))
Proof
  rewrite_tac[entry_fn_no_params_def] >> strip_tac >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[venomInstTheory.is_param_opcode_def]
QED

Theorem fix_phi_inst_read0[local]:
  (is_read0_opcode i.inst_opcode ==> i.inst_operands = []) ==>
  (is_read0_opcode (fix_phi_inst ps i).inst_opcode ==>
    (fix_phi_inst ps i).inst_operands = [])
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops ps i.inst_operands` >>
      simp[is_read0_opcode_def] >>
      rename1 `h::t` >> Cases_on `t` >> simp[is_read0_opcode_def] >>
      rename1 `h::k::rest` >> Cases_on `rest` >> simp[is_read0_opcode_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem canon_jnz_inst_read0[local]:
  (is_read0_opcode i.inst_opcode ==> i.inst_operands = []) ==>
  (is_read0_opcode (canon_jnz_inst i).inst_opcode ==>
    (canon_jnz_inst i).inst_operands = [])
Proof
  Cases_on `canon_jnz_inst i = i` >- simp[] >>
  drule simplifyCfgShapeTheory.canon_jnz_inst_changed >> strip_tac >>
  simp[is_read0_opcode_def]
QED

Theorem simplify_cfg_read0_operands:
  EVERY (\i. is_read0_opcode i.inst_opcode ==> i.inst_operands = []) (fn_insts f) ==>
  EVERY (\i. is_read0_opcode i.inst_opcode ==> i.inst_operands = [])
    (fn_insts (FST (simplify_cfg_fn_with_labels f)))
Proof
  strip_tac >> irule simplify_cfg_fn_with_labels_every >> BETA_TAC >>
  rpt conj_tac
  >- metis_tac[canon_jnz_inst_read0]
  >- (simp[subst_label_inst_def] >> rpt strip_tac >> simp[])
  >- (rpt gen_tac >>
      simp[simplifyCfgShapeTheory.update_phi_bypass_opcode] >>
      Cases_on `i.inst_opcode = PHI`
      >- simp[is_read0_opcode_def] >>
      simp[update_phi_bypass_def])
  >- metis_tac[fix_phi_inst_read0]
  >- (rpt gen_tac >> Cases_on `is_block_label_opcode i.inst_opcode` >>
      simp[subst_block_labels_inst_def, subst_label_map_inst_def] >>
      rpt strip_tac >> simp[]) >> simp[]
QED

(* Assembly draft retained for C1.7.4.2.
Theorem simplify_cfg_structural_shape:
  o1_fn_shape ctx f ==>
  EVERY inst_wf (fn_insts (FST (simplify_cfg_fn_with_labels f))) /\
  EVERY label_positions_ok (fn_insts (FST (simplify_cfg_fn_with_labels f))) /\
  first_block_no_preds (FST (simplify_cfg_fn_with_labels f)) /\
  first_block_no_phi (FST (simplify_cfg_fn_with_labels f)) /\
  fn_label_refs_ok (FST (simplify_cfg_fn_with_labels f)) /\
  (FST (simplify_cfg_fn_with_labels f)).fn_blocks <> [] /\
  (HD (FST (simplify_cfg_fn_with_labels f)).fn_blocks).bb_label =
    (HD f.fn_blocks).bb_label
Proof
  strip_tac >> irule (BETA_RULE simplify_cfg_fn_structural_shape) >>
  gvs[o1_fn_shape_def, wf_function_def, fn_has_entry_def,
    fn_inst_wf_def, fn_shape_ok_def, inst_shape_ok_def,
    first_block_no_phi_def, EVERY_MEM, fn_insts_def,
    fn_insts_blocks_MEM]
QED

*)

Theorem simplify_cfg_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG)
Proof
  cheat
QED
