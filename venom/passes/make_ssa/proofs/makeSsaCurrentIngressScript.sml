Theory makeSsaCurrentIngress
Ancestors makeSsaCurrentPlacement makeSsaCurrentPlacementCut
  makeSsaCurrentDefSupport makeSsaCurrentAnalysis makeSsaCurrentDefs
  makeSsaCurrentTree list sorting

Theorem current_pruned_reach_ingress:
  !h. current_pruned_reach df li v roots h ==>
    ?d. current_frontier_edge df d h /\
      (MEM d roots \/ (d <> h /\ current_pruned_reach df li v roots d))
Proof
  ho_match_mp_tac current_pruned_reach_strongind >> metis_tac[]
QED

Theorem current_actual_inserted_ingress:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_actual_inserted fn v h ==>
  ?d. current_frontier_edge (current_frontier_map fn) d h /\
    ((?bb inst. MEM bb fn.fn_blocks /\ bb.bb_label = d /\
       MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) \/
     (d <> h /\ current_actual_inserted fn v d))
Proof
  simp[current_actual_inserted_def] >> strip_tac >>
  drule current_pruned_reach_ingress >> strip_tac
  >- (drule_all compute_defs_support >> strip_tac >>
      drule_all current_ordered_blocks_perm >> strip_tac >>
      metis_tac[PERM_MEM_EQ]) >>
  metis_tac[]
QED
