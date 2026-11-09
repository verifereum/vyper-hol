(* Source-valid input transport at an actual endpoint. *)
Theory calldataValidObservations
Ancestors
  abiDecoderValidContract abiDecoderTypedContract abiDecoderContract
  venomState venomExecSemantics words list

Theorem calldata_valid_pre_observations:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap s /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  eval_operand src t = eval_operand src s /\
  eval_operand dst t = eval_operand dst s ==>
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap t
Proof
  simp[abi_decoder_valid_pre_def, abi_decoder_ranges_def, abi_decode_source_def] >>
  metis_tac[]
QED
