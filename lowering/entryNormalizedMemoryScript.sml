(* Transport decoder-normalized memory without identifying sparse values. *)
Theory entryNormalizedMemory
Ancestors
  entryAbiMemoryTransport abiDecoderLayout abiDecoderValidContract
  abiDecoderTypedContract valueEncoding vyperABI vyperTyping
  vyperTypeValues vyperValue vyperValueOperation

Theorem entry_decoder_normalized_memory:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_type env ty = SOME tv /\
  has_type (vyper_to_abi_type env ty) av /\
  value_has_type tv v /\ value_has_type tv nv /\
  vyper_to_abi env ty v = SOME av /\
  abi_to_vyper env ty av = SOME nv /\ val_in_memory tv nv p mem ==>
  val_in_memory tv v p mem
Proof
  strip_tac >> drule_all abi_decoder_typed_conversion >> strip_tac >>
  metis_tac[entry_common_conversion_memory]
QED

Theorem entry_valid_pre_original_memory:
  abi_decoder_valid_pre ce env sf ty tv bs nv st src dst opc (Lit 0w) hi 0 sb d b cap initial /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME (dec (vyper_to_abi_type env ty) bs) /\
  val_in_memory tv nv p mem ==>
  val_in_memory tv v p mem
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_metadata_def] >>
  rpt strip_tac >> irule entry_decoder_normalized_memory >> metis_tac[]
QED
