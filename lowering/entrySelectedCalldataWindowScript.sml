(* Source-selected calldata is preserved through the entry control prefix. *)
Theory entrySelectedCalldataWindow
Ancestors
  entryDispatchProps moduleLoweringProps vyperLoweringCorrect valueEncodingDefs
  abiDecoderContract valueEncoding list words

Theorem selector_prefixed_calldata_window[local]:
  s.vs_call_ctx.cc_calldata = function_selector fname ats ++ bs ==>
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
Proof
  strip_tac >>
  simp[abi_decode_source_def, mem_bytes_at_def,
       DROP_APPEND, function_selector_length, TAKE_APPEND1,
       DROP_LENGTH_TOO_LONG]
QED

Theorem selected_ready_calldata_window:
  initial_venom_state_rel tops am tx vs /\ source_typing_ok tops am tx /\
  vs.vs_call_ctx.cc_calldata = function_selector fname ats ++ bs /\
  vars_pc_only
    (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) t ==>
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD t) = bs /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256) /\
  4 + LENGTH bs < dimword (:256)
Proof
  strip_tac >> drule vars_pc_only_fields >> simp[] >> strip_tac >>
  drule_all initial_venom_state_calldata_length >> strip_tac >>
  `t.vs_call_ctx.cc_calldata = function_selector fname ats ++ bs` by simp[] >>
  drule selector_prefixed_calldata_window >> strip_tac >>
  gvs[function_selector_length]
QED
