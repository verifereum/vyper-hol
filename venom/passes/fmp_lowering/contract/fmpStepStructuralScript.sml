(* Checked block and entry structure transport for FMP lowering. *)
Theory fmpStepStructural
Ancestors
  fmpStepLayout fmpStepReclaim fmpStepRewrite fmpStepRestrictionClosure
  fmpLowerDefs fmpLowerProps venomExecProofs venomWf venomInst o1PassContract
  fmpStepPredicateTransport unitShapeDefs
  fmpStepList fmpStepChunk
  list rich_list finite_map alist

Theorem analyze_fmp_reclaims_not_phi:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\ wf_function fn /\
  MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  MEM ((bb.bb_label,n),target) (fmap_to_alist plan) ==>
  (EL n bb.bb_instructions).inst_opcode <> PHI
Proof
  strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `FLOOKUP plan (bb.bb_label,n) = SOME target` by
    gvs[MEM_fmap_to_alist_FLOOKUP] >>
  drule_all analyze_fmp_reclaims_position >> strip_tac >> gvs[] >>
  drule fmp_reclaim_point_not_prefix >> simp[]
QED

Theorem fmp_lower_checked_blocks_well_formed:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\ wf_function fn /\
  fmp_lower_blocks infos ctx runner s (fmap_to_alist plan) fn.fn_blocks =
    SOME (FmpBlocksResult out leftover s') ==>
  EVERY bb_well_formed out
Proof
  strip_tac >> drule fmp_lower_blocks_well_formed >>
  disch_then irule >> reverse conj_tac
  >- gvs[wf_function_def, EVERY_MEM] >>
  rpt strip_tac >> drule_all analyze_fmp_reclaims_not_phi >> simp[]
QED

Theorem list_terminal_strip_nonterminal_prefix:
  EVERY (\x. ~P x) prefix /\ list_terminal P (prefix ++ suffix) ==>
  list_terminal P suffix
Proof
  Induct_on `prefix` >> simp[list_terminal_def] >>
  rpt strip_tac >> Cases_on `prefix ++ suffix = []` >> gvs[]
QED

Theorem bb_well_formed_replace_phi_free_prefix:
  entry.bb_instructions = old ++ tail /\ bb_well_formed entry /\
  EVERY (\i. ~is_terminator i.inst_opcode) old /\
  EVERY (\i. ~is_terminator i.inst_opcode) new /\
  EVERY (\i. i.inst_opcode <> PHI) entry.bb_instructions /\
  EVERY (\i. i.inst_opcode <> PHI) new ==>
  bb_well_formed (entry with bb_instructions := new ++ tail)
Proof
  simp[bb_well_formed_list] >> strip_tac >>
  `list_terminal (\i. is_terminator i.inst_opcode) tail` by
    (irule list_terminal_strip_nonterminal_prefix >> metis_tac[]) >>
  `tail <> []` by (Cases_on `tail` >> gvs[list_terminal_def]) >>
  simp[list_terminal_append] >> irule list_prefix_none >> gvs[EVERY_APPEND]
QED

Theorem fmp_lower_blocks_first_no_phi:
  fmp_lower_blocks infos ctx runner s restores (entry::rest) =
    SOME (FmpBlocksResult out leftover s') /\
  EVERY (\i. i.inst_opcode <> PHI) entry.bb_instructions ==>
  out <> [] /\ EVERY (\i. i.inst_opcode <> PHI) (HD out).bb_instructions
Proof
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_lower_indexed_not_phi >> simp[]
QED

Theorem fmp_root_layout_nonterminal_not_phi:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') ==>
  EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> PHI)
    (OPTION_TO_LIST root ++ OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def, set_param_index_def, callLayoutDefsTheory.OPTION_TO_LIST_def,
      is_terminator_def] >>
  drule fmpStepRestrictionClosureTheory.split_fmp_entry_retpc_restrictions >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[is_terminator_def]
QED

Theorem fmp_install_checked_root_structure:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmap_to_alist plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  wf_function fn /\ first_block_no_phi fn ==>
  EVERY bb_well_formed out /\
  EVERY (\i. i.inst_opcode <> PHI) (HD out).bb_instructions
Proof
  strip_tac >>
  drule_all fmp_lower_checked_blocks_well_formed >> strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule fmp_root_layout_nonterminal_not_phi >> strip_tac >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (users ++ OPTION_TO_LIST oldpc)` by
    (Cases_on `oldpc` >>
     gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, EVERY_MEM] >>
     metis_tac[is_terminator_def]) >>
  `blocks <> [] /\ EVERY (\i. i.inst_opcode <> PHI) (HD blocks).bb_instructions` by
    (drule split_fmp_entry_reconstruct >> strip_tac >>
     gvs[first_block_no_phi_def] >>
     drule fmp_lower_blocks_first_no_phi >> simp[]) >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  `EVERY (\i. i.inst_opcode <> PHI) users /\
   EVERY (\i. i.inst_opcode <> PHI) tail` by gvs[EVERY_APPEND] >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[] >>
  (conj_tac >-
    (irule bb_well_formed_replace_phi_free_prefix >>
     gvs[EVERY_APPEND, EVERY_MEM] >>
     metis_tac[EVERY_APPEND, EVERY_MEM])) >>
  gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_lower_function_structure:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  wf_function fn /\ first_block_no_phi fn ==>
  EVERY bb_well_formed fn'.fn_blocks /\ first_block_no_phi fn'
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fmp_checked_seal_some >> gvs[fmp_seal_def] >>
  TRY (gvs[wf_function_def, first_block_no_phi_def, EVERY_MEM] >> NO_TAC) >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_install_checked_root_structure >> simp[first_block_no_phi_def]
QED

Theorem fmp_lower_function_blocks_well_formed:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  wf_function fn /\ first_block_no_phi fn ==>
  EVERY bb_well_formed fn'.fn_blocks
Proof
  metis_tac[fmp_lower_function_structure]
QED

Theorem fmp_lower_function_first_block_no_phi:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  wf_function fn /\ first_block_no_phi fn ==> first_block_no_phi fn'
Proof
  metis_tac[fmp_lower_function_structure]
QED

Theorem split_fmp_entry_retpc_every:
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) /\
  EVERY P (fn_insts fn) ==> EVERY P (OPTION_TO_LIST pc)
Proof
  strip_tac >> drule split_fmp_entry_reconstruct >> strip_tac >>
  Cases_on `pc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def,
    fn_insts_def, fn_insts_blocks_def, EVERY_APPEND]
QED

Theorem fmp_make_root_layout_wf:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') /\ EVERY inst_wf (fn_insts fn) ==>
  EVERY inst_wf (OPTION_TO_LIST root) /\ EVERY inst_wf (OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac split_fmp_entry_retpc_opcode >>
  drule_all split_fmp_entry_retpc_every >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def, set_param_index_def,
    mk_inst_def, inst_wf_def] >>
  rpt strip_tac >> gvs[inst_wf_def, set_param_index_def]
QED

Theorem fmp_make_root_layout_shape_ok:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') /\ EVERY inst_shape_ok (fn_insts fn) ==>
  EVERY inst_shape_ok (OPTION_TO_LIST root) /\ EVERY inst_shape_ok (OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac split_fmp_entry_retpc_opcode >>
  drule_all split_fmp_entry_retpc_every >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def, set_param_index_def,
    mk_inst_def, inst_shape_ok_def, is_read0_opcode_def, label_positions_ok_def,
    stackPlanTypesTheory.is_label_operand_def] >>
  rpt strip_tac >> gvs[inst_shape_ok_def, set_param_index_def,
    is_read0_opcode_def, label_positions_ok_def,
    stackPlanTypesTheory.is_label_operand_def]
QED

Theorem fn_inst_wf_fn_insts:
  fn_inst_wf fn <=> EVERY inst_wf (fn_insts fn)
Proof
  simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[]
QED

Theorem fmp_lower_function_inst_wf:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ fn_inst_wf fn ==> fn_inst_wf fn'
Proof
  simp[fn_inst_wf_fn_insts] >>
  strip_tac >> irule fmp_lower_function_every >>
  conj_tac >- metis_tac[fmp_emit_restores_wf] >>
  qexistsl [`ctx`, `fn`, `s`, `s'`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule fmp_lower_inst_wf >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[fmp_make_root_layout_wf]
QED

Theorem fmp_lower_function_inst_shape_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY inst_shape_ok (fn_insts fn) ==> EVERY inst_shape_ok (fn_insts fn')
Proof
  strip_tac >> irule fmp_lower_function_every >>
  conj_tac >- metis_tac[fmp_emit_restores_shape_ok] >>
  qexistsl [`ctx`, `fn`, `s`, `s'`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule fmp_lower_inst_shape_ok >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[fmp_make_root_layout_shape_ok]
QED

Theorem terminal_list_successors_last:
  list_terminal (\i. is_terminator i.inst_opcode) insts ==>
  insts <> [] /\ FLAT (MAP get_successors insts) = get_successors (LAST insts)
Proof
  Induct_on `insts` >> simp[list_terminal_def] >>
  Cases_on `insts` >> simp[list_terminal_def] >>
  rpt strip_tac >> gvs[get_successors_def]
QED

Theorem bb_well_formed_successors_mem:
  bb_well_formed bb ==>
  (MEM label (bb_succs bb) <=>
   MEM label (FLAT (MAP get_successors bb.bb_instructions)))
Proof
  simp[bb_well_formed_list] >> strip_tac >>
  drule terminal_list_successors_last >> strip_tac >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def]
QED

Theorem fmp_lower_function_successor_origin:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  wf_function fn /\ first_block_no_phi fn /\
  MEM bb fn'.fn_blocks /\ MEM label (bb_succs bb) ==>
  ?old. MEM old fn.fn_blocks /\ MEM label (bb_succs old)
Proof
  strip_tac >> drule_all fmp_lower_function_blocks_well_formed >> strip_tac >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  drule_all bb_well_formed_successors_mem >> strip_tac >>
  drule fmp_lower_function_preserves_successors >> strip_tac >>
  `MEM (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))
    (MAP (\b. (b.bb_label, FLAT (MAP get_successors b.bb_instructions))) fn.fn_blocks)` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> qexists `bb` >> simp[]) >>
  gvs[MEM_MAP] >> rename1 `MEM old fn.fn_blocks` >>
  qexists `old` >> simp[] >>
  `bb_well_formed old` by gvs[wf_function_def] >>
  drule bb_well_formed_successors_mem >> simp[]
QED

Theorem fmp_lower_function_succs_closed:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  wf_function fn /\ first_block_no_phi fn ==> fn_succs_closed fn'
Proof
  strip_tac >> simp[fn_succs_closed_def] >> rpt strip_tac >>
  drule_all fmp_lower_function_successor_origin >> strip_tac >>
  drule fmp_lower_function_preserves_labels >>
  gvs[wf_function_def, fn_succs_closed_def] >> metis_tac[]
QED

Theorem fmp_lower_function_first_block_no_preds:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  wf_function fn /\ first_block_no_phi fn /\ first_block_no_preds fn ==>
  first_block_no_preds fn'
Proof
  strip_tac >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (drule fmp_lower_function_preserves_labels >>
     Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[wf_function_def, fn_has_entry_def, fn_labels_def]) >>
  simp[first_block_no_preds_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all fmp_lower_function_successor_origin >> strip_tac >>
  gvs[first_block_no_preds_def, EVERY_MEM] >> metis_tac[]
QED
