(* Checked interface probe: ordinary site effects exclude reverting endpoints. *)
Theory exprSimAbiDecodeMemberReject
Ancestors
  exprSimAbiDecodeMemberOutcome abiDecoderSiteEffect venomState exprSimDefs

Theorem abi_decode_revert_not_static_frame:
  !s. ~s.vs_halted ==>
  ~decode_static_frame s (revert_state (set_returndata [] s))
Proof
  simp[decode_static_frame_def, revert_state_def, set_returndata_def,
    venom_state_component_equality]
QED

Theorem abi_decode_revert_not_site_effect:
  !s. ~s.vs_halted ==>
  ~decode_site_effect ctx fn next writes s (revert_state (set_returndata [] s))
Proof
  metis_tac [decode_site_effect_def, abi_decode_revert_not_static_frame]
QED

Theorem abi_decode_rejection_expr_exit:
  !res t.
  ((?m. res = INR (Error (RuntimeError m))) \/
   (?d. res = INR (Error (RevertData d))) \/
   (?str. res = INR (AssertException str))) ==>
  expr_exit res (Abort Revert_abort t)
Proof
  rpt strip_tac >> gvs[expr_exit_def]
QED
