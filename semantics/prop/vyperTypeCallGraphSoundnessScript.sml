(*
 * Proof-facing properties of the executable checked-contract call graph.
 *
 * TOP-LEVEL:
 * - check_contract_call_graph_acyclic
 * - contract_call_edges_function
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
