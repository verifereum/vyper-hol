(* Width-valid primitive decoder descriptors have an ABI inhabitant. *)
Theory abiDecoderWidthBoundary
Ancestors
  vyperTypeSystem abiDecoderCoherence abiDecoderWordTyped
  exprLowering compileEnv vyperABI vyperValue contractABI words

Theorem abi_decoder_base_width_inhabited:
  evaluate_type env (BaseT bt) = SOME tv /\
  abi_decode_bytes_widths env (BaseT bt) /\
  is_word_type (BaseT bt) ==>
  ?av. has_type (vyper_base_to_abi_type bt) av
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bd` >> Cases_on `bd`, all_tac] >>
  simp[evaluate_type_def, abi_decode_bytes_widths_def,
       is_word_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >>
  FIRST [
    (qexists_tac `NumV 0` >> simp[has_type_def, valid_int_bound_def] >> NO_TAC),
    (qexists_tac `contractABI$IntV 0` >> simp[has_type_def, valid_int_bound_def,
      int_bits_bound_def] >> NO_TAC),
    (qexists_tac `BoolV F` >> simp[has_type_def] >> NO_TAC),
    (qexists_tac `contractABI$BytesV (REPLICATE n 0w)` >> simp[has_type_def, dimword_def] >> NO_TAC)]
QED

Theorem abi_decoder_primitive_width_inhabited:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decode_bytes_widths env ty ==>
  ?av. has_type (vyper_to_abi_type env ty) av
Proof
  strip_tac >> drule_all abi_decoder_primitive_cases >> strip_tac
  >- (gvs[abi_decoder_coherent_base_iff, abi_decoder_header_def] >>
      simp[vyper_to_abi_type_def] >>
      irule abi_decoder_base_width_inhabited >> metis_tac[]) >>
  gvs[vyper_to_abi_type_def] >> qexists_tac `NumV 0` >>
  simp[has_type_def, valid_int_bound_def]
QED
