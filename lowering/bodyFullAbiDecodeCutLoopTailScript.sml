(* The selected dynamic-loop outcome, observed from its entered header. *)
Theory bodyFullAbiDecodeCutLoopTail
Ancestors
  bodyFullAbiDecodeRuntimeLoopObserved bodyFullAbiDecodeLoopBodyObserved
Libs
  bodyFullAbiDecodeRuntimeLoopLengthObservedLib

Theorem abi_decode_loop_after_entry_selected:
  ^observed_loop_length_split_entry_clause_typed
Proof
  let
    val norm = REDEPTH_CONV BETA_CONV THENC simpLib.SIMP_CONV bool_ss []
  in
    CONV_TAC norm >>
    mp_tac (CONV_RULE norm (Q.SPEC `T` abi_decode_dyn_loop_word_frame_split_entry)) >>
    (impl_tac >- ACCEPT_TAC (CONV_RULE norm abi_decode_loop_body_length_observed_conditional)) >>
    disch_then ACCEPT_TAC
  end
QED
