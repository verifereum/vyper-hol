(* The typed decoder's root validity test is the builtin's source result. *)
Theory abiDecodeMemBuiltinSource
Ancestors
  exprSimAbiDecodeBuiltinLayout exprSimAbiDecodeMinimumLayout
  exprSimAbiDecodeBuiltinSource exprSimAbiDecodeMemberExecute
  abiDecoderCoherence abiCallerAbiBound vyperABIValid vyperABI
  vyperValue vyperTypeABI contractABI compileEnv list

Theorem abi_decode_mem_builtin_source_iff:
  abi_decoder_coherent ce env sf ty tv /\
  abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty ==>
  ((vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      static_length (vyper_to_abi_type env ty) <= LENGTH bs) /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
    value_has_type tv v) <=> evaluate_abi_decode env ty bs = INL v)
Proof
  strip_tac >> drule abi_decode_coherent_minimum >> strip_tac >>
  drule abi_decode_coherent_bound >>
  simp_tac bool_ss [abi_caller_abi_bound_def] >> strip_tac >>
  `abi_static_length (vyper_to_abi_type env ty) <= LENGTH bs /\
   LENGTH bs <= vyper_abi_size_bound env ty` by metis_tac[] >>
  drule_all abi_decode_builtin_source_window >>
  simp_tac bool_ss [abi_decode_source_accepts_def] >> strip_tac >>
  eq_tac >- metis_tac[] >> strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `value_has_type tv v` by metis_tac[evaluate_abi_decode_well_typed] >>
  `is_dynamic (vyper_to_abi_type env ty) \/
   static_length (vyper_to_abi_type env ty) <= LENGTH bs` by
    metis_tac[evaluate_abi_decode_vyper_valid_enc, vyper_valid_enc_static_length_lower] >>
  metis_tac[]
QED
