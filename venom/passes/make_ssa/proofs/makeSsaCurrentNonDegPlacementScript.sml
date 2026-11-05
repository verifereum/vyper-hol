Theory makeSsaCurrentNonDegPlacement
Ancestors
  makeSsaCurrentPlacement makeSsaCurrentPlacementCut makeSsaCurrentDefSupport
  makeSsaCurrentAnalysis sorting

(* A recursive self-frontier cannot be the first cause of reachability. *)
Theorem current_pruned_reach_nonself_source:
  current_pruned_reach df li v roots y ==>
  ?d. current_frontier_edge df d y /\
      (MEM d roots \/ (d <> y /\ current_pruned_reach df li v roots d))
Proof
  qid_spec_tac `y` >>
  ho_match_mp_tac current_pruned_reach_strongind >>
  conj_tac
  >- (rpt strip_tac >> qexists_tac `d` >> simp[]) >>
  map_every qx_gen_tac [`source`, `target`] >>
  disch_tac >> Cases_on `source = target`
  >- (gvs[] >> metis_tac[]) >>
  qexists_tac `source` >> gvs[]
QED

Theorem current_actual_inserted_nonself_source:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME entry /\
  current_actual_inserted fn v y ==>
  ?d. current_frontier_edge (current_frontier_map fn) d y /\
      ((?bb inst. MEM bb fn.fn_blocks /\ bb.bb_label = d /\
          MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) \/
       (d <> y /\ current_actual_inserted fn v d))
Proof
  strip_tac >> drule_all current_ordered_blocks_perm >> strip_tac >>
  qpat_x_assum `current_actual_inserted _ _ _` mp_tac >>
  simp[current_actual_inserted_def] >> strip_tac >>
  drule current_pruned_reach_nonself_source >> strip_tac
  >- (drule_all compute_defs_support >> strip_tac >>
      qexists_tac `d` >> simp[] >> disj1_tac >>
      qexistsl_tac [`bb`, `inst`] >> simp[] >>
      metis_tac[PERM_MEM_EQ]) >>
  qexists_tac `d` >> simp[current_actual_inserted_def] >>
  disj2_tac >> goal_assum $ drule_at Any
QED
