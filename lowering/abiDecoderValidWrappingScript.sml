(* Source type coherence for either actual singleton-wrapping choice. *)
Theory abiDecoderValidWrapping
Ancestors
  abiCallerDecodeBounds abiDecoderCaller abiDecoderCoherence abiDecoderReadableTypes
  abiBoundaryChecks compileEnv valueEncoding vyperABI vyperValue list

Theorem abi_decoder_coherent_singleton:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_coherent ce env sf (TupleT [ty]) (TupleTV [tv])
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  `evaluate_type env ty = SOME tv` by fs[abi_decoder_header_def] >>
  drule abi_caller_singleton_type >> strip_tac >>
  irule decoder_caller_singleton >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_wrapping:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_coherent ce env sf (if wrapped then TupleT [ty] else ty)
    (if wrapped then TupleTV [tv] else tv)
Proof
  strip_tac >> Cases_on `wrapped` >> simp[abi_decoder_coherent_singleton]
QED
