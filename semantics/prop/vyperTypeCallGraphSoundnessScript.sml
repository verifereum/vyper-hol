(*
 * Proof-facing properties of the executable checked-contract call graph.
 *
 * TOP-LEVEL:
 * - check_contract_call_graph_acyclic
 * - contract_call_edges_function
 *)

Theory vyperTypeCallGraphSoundness
Ancestors
  arithmetic list vyperTypeCallGraph vyperTypeContract

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
