Theory fmpStageCoverBackScfgStructure
Ancestors
  fmpStageRel fmpStepStructural fmpStepLayout fmpStepRestrictions
  o1MakeSsaFormats o1MakeSsaStructuralShape o1MakeSsaCfg
  o1MakeSsaFrontier makeSsaCurrentFrontier makeSsaCurrentProps
  cfgHelpers cfgDefs makeSsaDefs o1PassContract unitShapeDefs venomWf
  venomInst list rich_list arithmetic

(* Only the structural projections required by SimplifyCFG are transported;
   neither transformation's global instruction-ID invariant is needed. *)
Theorem fmp_cover_back_lower_structure:
  fmp_stage_lowered infos ctx runner fn lowered /\ o1_fn_shape C fn ==>
  ALL_DISTINCT (fn_labels lowered) /\ lowered.fn_blocks <> [] /\
  EVERY bb_well_formed lowered.fn_blocks /\
  EVERY inst_wf (fn_insts lowered) /\
  EVERY inst_shape_ok (fn_insts lowered) /\
  first_block_no_preds lowered /\ fn_succs_closed lowered /\
  first_block_no_phi lowered /\ fn_label_refs_ok lowered
Proof
  strip_tac >>
  `?sp sp'. fmp_lower_function ctx sp fn = SOME (lowered,sp')` by
    (gvs[fmp_stage_lowered_def, fmpLowerDefsTheory.fmp_lower_function_def] >>
     metis_tac[]) >>
  `wf_function fn /\ first_block_no_phi fn /\ first_block_no_preds fn /\
   fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) /\ fn_label_refs_ok fn` by
    gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule_all fmp_lower_function_structure >> strip_tac >>
  drule_all fmp_lower_function_first_block_no_preds >> strip_tac >>
  drule_all fmp_lower_function_succs_closed >> strip_tac >>
  drule_all fmp_lower_function_inst_wf >> strip_tac >>
  drule_all fmp_lower_function_inst_shape_ok >> strip_tac >>
  drule_all fmp_lower_function_label_refs_ok >> strip_tac >>
  drule fmp_lower_function_preserves_labels >> strip_tac >>
  gvs[fn_inst_wf_fn_insts, wf_function_def, fn_has_entry_def] >>
  Cases_on `fn.fn_blocks` >> Cases_on `lowered.fn_blocks` >> gvs[fn_labels_def]
QED

Theorem fmp_cover_back_make_ssa_structure[local]:
  ALL_DISTINCT (fn_labels fn) /\ fn.fn_blocks <> [] /\
  EVERY bb_well_formed fn.fn_blocks /\ EVERY inst_wf (fn_insts fn) /\
  EVERY inst_shape_ok (fn_insts fn) /\ first_block_no_preds fn /\
  fn_succs_closed fn /\ first_block_no_phi fn /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ALL_DISTINCT (fn_labels fn') /\ fn'.fn_blocks <> [] /\
  EVERY bb_well_formed fn'.fn_blocks /\ EVERY inst_wf (fn_insts fn') /\
  EVERY label_positions_ok (fn_insts fn') /\ first_block_no_preds fn' /\
  fn_succs_closed fn' /\ first_block_no_phi fn'
Proof
  strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  drule_all make_ssa_current_fn_blocks_well_formed >> strip_tac >>
  `fn_inst_wf fn` by simp[fn_inst_wf_fn_insts] >>
  drule_all make_ssa_current_fn_inst_wf >> strip_tac >>
  drule_all make_ssa_current_fn_instruction_shapes >> strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks)` by
    (pure_once_rewrite_tac[GSYM bb_label_eta] >> gvs[fn_labels_def]) >>
  drule_all make_ssa_current_fn_first_block_no_preds >> strip_tac >>
  drule_all make_ssa_current_fn_cfg_blocks >> strip_tac >>
  drule_all make_ssa_current_fn_first_block_no_phi >> strip_tac >>
  `fn_succs_closed fn'` by
    (fs[fn_succs_closed_def] >> rpt strip_tac >>
     `MEM (bb.bb_label,bb_succs bb)
       (MAP (\b. (b.bb_label,bb_succs b)) fn.fn_blocks)` by
       (qpat_x_assum `MAP (\b. (b.bb_label,bb_succs b)) _ = _`
          (fn th => pure_rewrite_tac[GSYM th]) >> simp[MEM_MAP] >> metis_tac[]) >>
     gvs[MEM_MAP, fn_labels_def] >> metis_tac[]) >>
  gvs[fn_labels_def, fn_inst_wf_fn_insts, EVERY_MEM, inst_shape_ok_def] >>
  Cases_on `fn'.fn_blocks` >> gvs[]
QED

Theorem fmp_cover_back_stage_make_ssa_structure:
  fmp_stage_lowered infos ctx runner fn lowered /\ o1_fn_shape C fn /\
  make_ssa_current_fn s lowered = (fn',s') ==>
  ALL_DISTINCT (fn_labels fn') /\ fn'.fn_blocks <> [] /\
  EVERY bb_well_formed fn'.fn_blocks /\ EVERY inst_wf (fn_insts fn') /\
  EVERY label_positions_ok (fn_insts fn') /\ first_block_no_preds fn' /\
  fn_succs_closed fn' /\ first_block_no_phi fn'
Proof
  strip_tac >> drule_all fmp_cover_back_lower_structure >> strip_tac >>
  drule_all fmp_cover_back_make_ssa_structure >> simp[]
QED
