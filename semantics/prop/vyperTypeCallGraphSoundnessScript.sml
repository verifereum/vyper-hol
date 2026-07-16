(*
 * Proof-facing properties of the executable checked-contract call graph.
 *
 * TOP-LEVEL:
 * - check_contract_call_graph_acyclic
 * - contract_call_edges_function
 *)

Theory vyperTypeCallGraphSoundness
Ancestors
  list vyperTypeCallGraph vyperTypeContract

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
