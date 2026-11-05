Theory makeSsaCurrentSingleSiteSegment
Ancestors
  makeSsaCurrentPlacementCut makeSsaCurrentOccurrence makeSsaCurrentLastSite
  makeSsaCurrentRestrictedSegment

Theorem current_single_definition_changing_site_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME entry /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  blocks_have_leading_phi fn.fn_blocks /\
  current_changing_site fn (current_actual_inserted fn) v l ==>
  l = db.bb_label
Proof
  simp[current_changing_site_def] >> rpt strip_tac
  >- (drule_all current_actual_inserted_single_local >> simp[]) >>
  metis_tac[current_single_def_occurrence]
QED
