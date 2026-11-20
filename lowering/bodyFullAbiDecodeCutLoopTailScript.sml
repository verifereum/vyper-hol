(* The selected dynamic-loop outcome, observed from its entered header. *)
Theory bodyFullAbiDecodeCutLoopTail
Ancestors
  bodyFullAbiDecodeRuntimeLoopObserved bodyFullAbiDecodeLoopBodyObserved
Libs
  bodyFullAbiDecodeRuntimeLoopLengthObservedLib

Theorem abi_decode_loop_after_entry_selected:
  ^observed_loop_length_split_entry_clause_typed
Proof
  ACCEPT_TAC (MP
    (PURE_REWRITE_RULE [CONJUNCT1 (SPEC_ALL boolTheory.IMP_CLAUSES)]
      (SPEC T abi_decode_dyn_loop_word_frame_split_entry))
    abi_decode_loop_body_length_observed_conditional)
QED
