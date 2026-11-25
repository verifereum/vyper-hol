Theory whitelistCheckerCallGraphProps
Ancestors
  vyperTypeContract vyperTypeCallGraph vyperTypeCallGraphSoundness relation list

Theorem checked_no_self_call:
  check_contract mode layouts addr mods = SOME art ==>
  ~MEM (k,k) (contract_call_edges mods)
Proof
  strip_tac >> drule checked_contract_call_graph_irreflexive >>
  rw[relationTheory.irreflexive_def] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  irule relationTheory.TC_SUBSET >> fs[call_edge_rel_def]
QED
