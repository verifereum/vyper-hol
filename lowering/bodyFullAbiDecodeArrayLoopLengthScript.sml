Theory bodyFullAbiDecodeArrayLoopLength
Ancestors
  bodyFullAbiDecodeRuntimeLoopLengthObserved bodyFullAbiDecodeLoopBodyObserved
Libs
  bodyFullAbiDecodeRuntimeLoopLengthObservedLib

Theorem abi_decode_dyn_loop_length_observed_conditional:
  ^observed_loop_length_clause_typed
Proof
  ACCEPT_TAC (MP abi_decode_dyn_loop_length_from_body
                 abi_decode_loop_body_length_observed_conditional)
QED
