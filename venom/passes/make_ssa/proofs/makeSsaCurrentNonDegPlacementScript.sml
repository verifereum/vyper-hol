Theory makeSsaCurrentNonDegPlacement
Ancestors
  makeSsaCurrentPlacement

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
