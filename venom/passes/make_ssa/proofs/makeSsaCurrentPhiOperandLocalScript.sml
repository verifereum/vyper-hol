Theory makeSsaCurrentPhiOperandLocal
Ancestors makeSsaCurrentDemandedCut makeSsaCurrentPlacementCut
  makeSsaCurrentPlacement makeSsaCurrentSelectedLive makeSsaCurrentMergeSeed
  makeSsaCurrentDefs makeSsaCurrentAnalysis livenessTransferProofs
  livenessDefs venomWf venomExecProps venomInst cfgWf list alist

Theorem current_collected_index_phi[local]:
  !insts j. j < LENGTH (collect_phis insts) ==>
    j < LENGTH insts /\ (EL j insts).inst_opcode = PHI
Proof
  Induct >> simp[collect_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `j` >> simp[]
QED

Theorem current_inserted_phi_operand_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) /\
  MEM v (MAP SND (phi_pairs phi.inst_operands)) ==>
  ?bb j. lookup_block h fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    (EL j bb.bb_instructions).inst_outputs = [v]
Proof
  strip_tac >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    metis_tac[current_phi_operand_single_bound] >>
  `blocks_have_leading_phi fn.fn_blocks` by
    metis_tac[current_phi_operand_has_leading_phi] >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  `fn_reachable fn h` by metis_tac[current_all_labels_reachable, current_cfg_reachable] >>
  `?bb. lookup_block h fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP, wf_function_def] >> metis_tac[MEM_lookup_block]) >>
  `?vs. ALOOKUP (select_current_live_in T (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs` by
    (qpat_x_assum `current_actual_inserted _ _ _` mp_tac >>
     simp[current_actual_inserted_def] >>
     metis_tac[current_pruned_reach_live, current_placement_live_def]) >>
  drule_all current_selected_live_single_definition >> strip_tac >>
  `h = db.bb_label` by metis_tac[current_actual_inserted_single_local] >>
  `db = bb` by
    (`lookup_block h fn.fn_blocks = SOME db` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  gvs[] >>
  `j < LENGTH bb.bb_instructions /\ (EL j bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[current_collected_index_phi] >>
  `inst_wf (EL j bb.bb_instructions)` by metis_tac[fn_inst_wf_def, MEM_EL] >>
  `LENGTH (EL j bb.bb_instructions).inst_outputs = 1` by gvs[inst_wf_def] >>
  qexists_tac `j` >> simp[] >>
  Cases_on `(EL j bb.bb_instructions).inst_outputs` >> gvs[LENGTH_EQ_NUM]
QED
