(* Exact reconstruction of DFG records, including complete record literals. *)
Theory venomDfgRecordCases
Ancestors
  dfgDefs

Theorem dfg_analysis_eta:
  !state. state =
    dfg_analysis state.dfg_uses state.dfg_defs state.dfg_ids
Proof
  gen_tac >> Cases_on `state` >> simp[]
QED

