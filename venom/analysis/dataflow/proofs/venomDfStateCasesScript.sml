(* Reconstruct dataflow records without evaluating their map contents. *)
Theory venomDfStateCases
Ancestors
  dfAnalyzeDefs

Theorem df_state_eta:
  !state : 'a df_state.
    state = df_state state.ds_inst state.ds_boundary
Proof
  gen_tac >> Cases_on `state` >> simp[]
QED

