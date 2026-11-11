Theory targetCallReachClosure
Ancestors
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperSubscriptOverlap pred_set list

Theorem reachable_nodes_step_members[local]:
  MEM y (reachable_nodes edges (SUC n) seed) <=>
  MEM y (reachable_nodes edges n seed) \/
  ?x. MEM x (reachable_nodes edges n seed) /\ MEM (x,y) edges
Proof
  simp[reachable_nodes_def, MEM_nub, MEM_FLAT, MEM_MAP,
       MEM_direct_callees, call_edge_rel_def, PULL_EXISTS]
QED

Theorem reachable_nodes_step_subset[local]:
  set (reachable_nodes edges n seed) SUBSET
  set (reachable_nodes edges (SUC n) seed)
Proof
  simp[SUBSET_DEF, reachable_nodes_step_members]
QED

Theorem reachable_nodes_step_cong[local]:
  set (reachable_nodes edges n seed) = set (reachable_nodes edges m seed) ==>
  set (reachable_nodes edges (SUC n) seed) =
  set (reachable_nodes edges (SUC m) seed)
Proof
  simp[EXTENSION, reachable_nodes_step_members] >> metis_tac[]
QED

Theorem reachable_nodes_empty_plateau[local]:
  set (reachable_nodes edges n seed) = {} ==>
  set (reachable_nodes edges (SUC n) seed) = set (reachable_nodes edges n seed)
Proof
  simp[EXTENSION, reachable_nodes_step_members] >> metis_tac[]
QED

Theorem finite_chain_growth[local]:
  !n f.
  (!k. FINITE (f k)) /\
  (!k. f k SUBSET f (SUC k)) /\
  (!k. f k = f (SUC k) ==> f (SUC k) = f (SUC (SUC k))) /\
  (f 0 = {} ==> f 0 = f 1) ==>
  f n = f (SUC n) \/ SUC n <= CARD (f n)
Proof
  Induct >> rpt strip_tac
  >- (qpat_x_assum `!k. f k = f (SUC k) ==> _` kall_tac >>
      Cases_on `f 0 = {}`
      >- (disj1_tac >> gvs[]) >>
      disj2_tac >>
      `CARD (f 0) <> 0` by simp[CARD_EQ_0] >> decide_tac) >>
  qpat_x_assum `!f. _` (qspec_then `f` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac
  >- (disj1_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  Cases_on `f n = f (SUC n)`
  >- metis_tac[] >>
  `f n PSUBSET f (SUC n)` by simp[PSUBSET_DEF] >>
  `CARD (f n) < CARD (f (SUC n))` by metis_tac[CARD_PSUBSET] >>
  disj2_tac >> decide_tac
QED

Theorem reachable_nodes_endpoints[local]:
  !n seed. set (reachable_nodes edges n seed) SUBSET
    set (nub (MAP FST edges ++ MAP SND edges))
Proof
  Induct
  >- (simp[reachable_nodes_def, SUBSET_DEF, MEM_direct_callees,
           call_edge_rel_def, MEM_MAP, PULL_EXISTS] >>
      metis_tac[pairTheory.SND]) >>
  gvs[SUBSET_DEF, MEM_nub, MEM_APPEND, MEM_MAP] >>
  simp[reachable_nodes_step_members, PULL_EXISTS] >>
  rpt strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexists_tac `(x',x)` >> simp[]
QED

Theorem reachable_nodes_saturated[local]:
  set (reachable_nodes edges (LENGTH (nub (MAP FST edges ++ MAP SND edges))) seed) =
  set (reachable_nodes edges (SUC (LENGTH (nub (MAP FST edges ++ MAP SND edges)))) seed)
Proof
  qspec_then `LENGTH (nub (MAP FST edges ++ MAP SND edges))` mp_tac finite_chain_growth >>
  disch_then (qspec_then `\k. set (reachable_nodes edges k seed)` mp_tac) >>
  simp[] >>
  (impl_tac
   >- (rpt conj_tac
       >- simp[reachable_nodes_step_subset]
       >- metis_tac[reachable_nodes_step_cong]
       >> (mp_tac (Q.INST [`n` |-> `0`] reachable_nodes_empty_plateau) >> simp[]))) >>
  strip_tac >>
  `CARD (set (reachable_nodes edges (LENGTH (nub (MAP FST edges ++ MAP SND edges))) seed)) <=
   CARD (set (nub (MAP FST edges ++ MAP SND edges)))` by
    (irule CARD_SUBSET >> simp[reachable_nodes_endpoints]) >>
  `CARD (set (nub (MAP FST edges ++ MAP SND edges))) <=
   LENGTH (nub (MAP FST edges ++ MAP SND edges))` by simp[CARD_LIST_TO_SET] >>
  gvs[]
QED

Theorem reachable_nodes_edge_closed:
  !edges seed x y.
  MEM x (reachable_nodes edges (LENGTH (nub (MAP FST edges ++ MAP SND edges))) seed) /\
  MEM (x,y) edges ==>
  MEM y (reachable_nodes edges (LENGTH (nub (MAP FST edges ++ MAP SND edges))) seed)
Proof
  rpt strip_tac >>
  mp_tac reachable_nodes_saturated >>
  simp[EXTENSION, reachable_nodes_step_members] >> metis_tac[]
QED

Theorem direct_edge_reachable[local]:
  MEM (x,y) edges ==> MEM y (reachable_nodes edges fuel x)
Proof
  strip_tac >> simp[MEM_reachable_nodes_NRC] >>
  qexists_tac `1` >> simp[call_edge_rel_def]
QED

Theorem reached_functions_edge_closed:
  MEM fn (reached_functions mods e) /\
  MEM (fn,callee) (contract_call_edges mods) ==>
  MEM callee (reached_functions mods e)
Proof
  simp[reached_functions_def, MEM_nub, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  strip_tac
  >- (disj2_tac >> qexists_tac `fn` >>
      simp[direct_edge_reachable]) >>
  disj2_tac >> qexists_tac `y` >> simp[] >>
  gvs[contract_call_nodes_def] >>
  irule reachable_nodes_edge_closed >> metis_tac[]
QED
