(* Observation bridge for the actual decoded entry endpoint. *)
Theory entryOwnedEndpointObservations
Ancestors entryDecoderStateFrame moduleLoweringProps venomState

Theorem vars_pc_only_entry_decoder_obs:
  vars_pc_only s t ==> entry_decoder_obs s t
Proof
  simp[vars_pc_only_def, venom_state_component_equality,
       entry_decoder_obs_def]
QED

Theorem entry_owned_endpoint_observations:
  vars_pc_only
    (s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  entry_decoder_obs t out ==> entry_decoder_obs s out
Proof
  simp[vars_pc_only_def, venom_state_component_equality,
       entry_decoder_obs_def] >> metis_tac[]
QED

Theorem entry_decoder_obs_gas_readings:
  entry_decoder_obs s out ==> out.vs_gas_readings = s.vs_gas_readings
Proof
  simp[entry_decoder_obs_def]
QED
