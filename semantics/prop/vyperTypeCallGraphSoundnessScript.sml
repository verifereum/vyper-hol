(*
 * Proof-facing properties of the executable checked-contract call graph.
 *
 * TOP-LEVEL:
 * - check_contract_call_graph_acyclic
 * - contract_call_edges_function
 * - contract_edges_respect_rank
 * - contract_call_graph_cycle
 *)

Theory vyperTypeCallGraphSoundness
Ancestors
  arithmetic list pred_set vyperTypeCallGraph vyperTypeContract

(* ===== Generic executable/declarative reachability boundary ===== *)

Definition call_edge_rel_def:
  call_edge_rel edges caller callee <=> MEM (caller,callee) edges
End

Theorem MEM_direct_callees:
  MEM callee (direct_callees edges caller) <=>
  call_edge_rel edges caller callee
Proof
  simp[direct_callees_def, call_edge_rel_def, MEM_MAP, MEM_FILTER] >>
  eq_tac
  >- (strip_tac >> PairCases_on `y` >> gvs[]) >>
  strip_tac >>
  qexists_tac `(caller,callee)` >>
  simp[]
QED

Theorem MEM_reachable_nodes_NRC:
  MEM callee (reachable_nodes edges fuel caller) <=>
  ?n. 0 < n /\ n <= SUC fuel /\
      NRC (call_edge_rel edges) n caller callee
Proof
  qid_spec_tac `callee` >>
  Induct_on `fuel`
  >- (gen_tac >>
      simp[reachable_nodes_def, MEM_direct_callees] >>
      eq_tac
      >- (strip_tac >> qexists_tac `1` >> simp[]) >>
      strip_tac >>
      `n = 1` by decide_tac >>
      gvs[]) >>
  gen_tac >>
  simp[reachable_nodes_def, MEM_nub, MEM_FLAT, MEM_MAP,
       MEM_direct_callees, PULL_EXISTS] >>
  eq_tac
  >- (strip_tac
      >- (qexists_tac `n` >> simp[] >> decide_tac) >>
      qexists_tac `SUC n` >>
      simp[NRC_SUC_RECURSE_LEFT] >>
      qexists_tac `y` >>
      simp[] >> decide_tac) >>
  strip_tac >>
  Cases_on `n <= SUC fuel`
  >- (disj1_tac >> qexists_tac `n` >> simp[]) >>
  `n = SUC (SUC fuel)` by decide_tac >>
  gvs[NRC_SUC_RECURSE_LEFT] >>
  disj2_tac >>
  qexistsl_tac [`z`, `SUC fuel`] >>
  simp[NRC_SUC_RECURSE_LEFT] >>
  metis_tac[]
QED

Theorem LRC_APPEND:
  LRC R (l1 ++ l2) x z <=>
  ?y. LRC R l1 x y /\ LRC R l2 y z
Proof
  qid_spec_tac `x` >>
  Induct_on `l1` >>
  simp[LRC_def] >>
  metis_tac[]
QED

Theorem not_ALL_DISTINCT_split:
  ~ALL_DISTINCT ls ==>
  ?p q r e. ls = p ++ e::q ++ e::r
Proof
  Induct_on `ls`
  >- simp[] >>
  gen_tac >> disch_tac >>
  Cases_on `MEM h ls`
  >- (fs[MEM_SPLIT] >>
      qexistsl_tac [`[]`, `l1`, `l2`, `h`] >>
      simp[]) >>
  gvs[] >>
  qexistsl_tac [`h::p`, `q`, `r`, `e`] >>
  simp[]
QED

Theorem LRC_not_ALL_DISTINCT_shorten:
  LRC R ls x x /\ ~ALL_DISTINCT ls ==>
  ?m. 0 < m /\ m < LENGTH ls /\ NRC R m x x
Proof
  strip_tac >>
  drule not_ALL_DISTINCT_split >>
  strip_tac >>
  gvs[LRC_APPEND, LRC_def] >>
  qexists_tac `LENGTH (p ++ e::r)` >>
  simp[NRC_LRC] >>
  qexists_tac `p ++ e::r` >>
  simp[LRC_APPEND, LRC_def] >>
  metis_tac[]
QED

Theorem finite_TC_self_NRC_bound:
  (!x y. R x y ==> MEM x nodes /\ MEM y nodes) ==>
  TC R x x ==>
  ?n. 0 < n /\ n <= LENGTH nodes /\ NRC R n x x
Proof
  rpt strip_tac >>
  `?n. 0 < n /\ NRC R n x x` by
    (gvs[TC_eq_NRC] >>
     qexists_tac `SUC n` >> simp[]) >>
  qspec_then `\m. 0 < m /\ NRC R m x x` mp_tac WOP >>
  (impl_tac
   >- (qexists_tac `n` >> simp[])) >>
  strip_tac >>
  fs[NRC_LRC] >>
  `ALL_DISTINCT ls'` by
    (spose_not_then assume_tac >>
     drule_all LRC_not_ALL_DISTINCT_shorten >>
     fs[NRC_LRC] >>
     metis_tac[]) >>
  `set ls' SUBSET set nodes` by
    (rw[SUBSET_DEF] >>
     drule_all LRC_MEM >>
     metis_tac[]) >>
  qexists_tac `n'` >>
  simp[] >>
  `CARD (set ls') <= CARD (set nodes)` by
    metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET] >>
  `CARD (set nodes) <= LENGTH nodes` by
    simp[CARD_LIST_TO_SET] >>
  conj_tac
  >- (`CARD (set ls') = LENGTH ls'` by
        simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
      decide_tac) >>
  qexists_tac `ls'` >>
  simp[]
QED
Theorem call_graph_acyclic_correct:
  (!caller callee.
     MEM (caller,callee) edges ==>
     MEM caller nodes /\ MEM callee nodes) ==>
  (call_graph_acyclic nodes edges <=>
   irreflexive (TC (call_edge_rel edges)))
Proof
  strip_tac >>
  simp[call_graph_acyclic_def, relationTheory.irreflexive_def] >>
  eq_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      `!a b. call_edge_rel edges a b ==>
             MEM a nodes /\ MEM b nodes` by
        metis_tac[call_edge_rel_def] >>
      `MEM x nodes` by
        (drule relationTheory.TC_CASES1_E >>
         strip_tac >> metis_tac[]) >>
      drule_all finite_TC_self_NRC_bound >>
      strip_tac >>
      `MEM x (reachable_nodes edges (LENGTH nodes) x)` by
        (simp[MEM_reachable_nodes_NRC] >>
         qexists_tac `n` >> simp[] >> decide_tac) >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  strip_tac >>
  simp[EVERY_MEM] >>
  rpt strip_tac >>
  spose_not_then assume_tac >>
  fs[MEM_reachable_nodes_NRC] >>
  Cases_on `n` >>
  gvs[TC_eq_NRC]
QED

(* ===== Topological-rank certificate soundness ===== *)

Theorem edges_respect_rank_edge:
  edges_respect_rank ranks edges /\ call_edge_rel edges caller callee ==>
  rank_lt ranks caller callee
Proof
  rw[edges_respect_rank_def, EVERY_MEM, call_edge_rel_def] >>
  first_x_assum (qspec_then `(caller,callee)` mp_tac) >>
  simp[]
QED

Theorem rank_lt_transitive:
  transitive (rank_lt ranks)
Proof
  rw[relationTheory.transitive_def] >>
  Cases_on `ALOOKUP ranks x` >>
  Cases_on `ALOOKUP ranks y` >>
  Cases_on `ALOOKUP ranks z` >>
  gvs[rank_lt_def] >>
  match_mp_tac (DECIDE ``!a b c:num. a < b /\ b < c ==> a < c``) >>
  simp[]
QED

Theorem edges_respect_rank_TC:
  edges_respect_rank ranks edges /\
  TC (call_edge_rel edges) caller callee ==>
  rank_lt ranks caller callee
Proof
  strip_tac >>
  qpat_x_assum `TC _ _ _` mp_tac >>
  qid_spec_tac `callee` >> qid_spec_tac `caller` >>
  ho_match_mp_tac relationTheory.TC_INDUCT >>
  metis_tac[edges_respect_rank_edge, rank_lt_transitive,
            relationTheory.transitive_def]
QED

Theorem edges_respect_rank_irreflexive:
  edges_respect_rank ranks edges ==>
  irreflexive (TC (call_edge_rel edges))
Proof
  rw[relationTheory.irreflexive_def] >>
  strip_tac >>
  drule_all edges_respect_rank_TC >>
  Cases_on `ALOOKUP ranks x` >>
  gvs[rank_lt_def]
QED

(* ===== Concrete cycle certificate soundness ===== *)

Theorem RTC_then_R_TC_call_graph[local]:
  RTC R x y /\ R y z ==> TC R x z
Proof
  metis_tac[relationTheory.RTC_CASES_TC, relationTheory.TC_RULES]
QED

Theorem call_path_RTC:
  call_path edges path /\ path <> [] ==>
  RTC (call_edge_rel edges) (HD path) (LAST path)
Proof
  Induct_on `path` >> simp[call_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[call_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >>
  simp[call_edge_rel_def]
QED

Theorem call_graph_cycle_not_irreflexive:
  call_graph_cycle edges path ==>
  ~irreflexive (TC (call_edge_rel edges))
Proof
  Cases_on `path` >> simp[call_graph_cycle_def] >>
  strip_tac >>
  `RTC (call_edge_rel edges) (HD (h::t)) (LAST (h::t))` by
    (irule call_path_RTC >> simp[]) >>
  fs[] >>
  rw[relationTheory.irreflexive_def] >>
  qexists_tac `h` >>
  irule RTC_then_R_TC_call_graph >>
  qexists_tac `LAST (h::t)` >>
  simp[call_edge_rel_def]
QED

(* ===== Checker consequence ===== *)

Theorem check_contract_call_graph_acyclic:
  check_contract in_deploy layouts addr mods = SOME art ==>
  contract_call_graph_acyclic mods
Proof
  simp[check_contract_def, AllCaseEqs()]
QED

(* ===== Edge introduction from a function declaration ===== *)

Theorem module_call_edges_function:
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tls /\
  MEM callee (function_int_calls dflts body) ==>
  MEM ((src,fn),callee) (module_call_edges (src,tls))
Proof
  rw[module_call_edges_def] >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `MAP (\callee. ((src,fn),callee))
    (function_int_calls dflts body)` >>
  simp[] >>
  conj_tac
  >- (qexists_tac `FunctionDecl vis mut nr raw fn args dflts ret body` >>
      simp[toplevel_call_edges_def]) >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem contract_call_edges_function:
  MEM (src,tls) mods /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tls /\
  MEM callee (function_int_calls dflts body) ==>
  MEM ((src,fn),callee) (contract_call_edges mods)
Proof
  rw[contract_call_edges_def] >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `module_call_edges (src,tls)` >>
  simp[] >>
  conj_tac
  >- (qexists_tac `(src,tls)` >> simp[]) >>
  metis_tac[module_call_edges_function]
QED

Theorem contract_call_edge_nodes:
  MEM edge (contract_call_edges mods) ==>
  MEM (FST edge) (contract_call_nodes mods) /\
  MEM (SND edge) (contract_call_nodes mods)
Proof
  rw[contract_call_nodes_def, MEM_nub] >>
  metis_tac[MEM_MAP]
QED

Theorem contract_call_graph_acyclic_correct:
  contract_call_graph_acyclic mods <=>
  irreflexive (TC (call_edge_rel (contract_call_edges mods)))
Proof
  simp[contract_call_graph_acyclic_def] >>
  irule call_graph_acyclic_correct >>
  rpt strip_tac >>
  drule contract_call_edge_nodes >>
  simp[]
QED

Theorem contract_edges_respect_rank:
  edges_respect_rank ranks (contract_call_edges mods) ==>
  contract_call_graph_acyclic mods
Proof
  strip_tac >>
  simp[contract_call_graph_acyclic_correct] >>
  metis_tac[edges_respect_rank_irreflexive]
QED

Theorem contract_call_graph_cycle:
  call_graph_cycle (contract_call_edges mods) path ==>
  ~contract_call_graph_acyclic mods
Proof
  strip_tac >>
  simp[contract_call_graph_acyclic_correct] >>
  metis_tac[call_graph_cycle_not_irreflexive]
QED

Theorem checked_contract_call_graph_irreflexive:
  check_contract in_deploy layouts addr mods = SOME art ==>
  irreflexive (TC (call_edge_rel (contract_call_edges mods)))
Proof
  strip_tac >>
  drule check_contract_call_graph_acyclic >>
  simp[contract_call_graph_acyclic_correct]
QED
