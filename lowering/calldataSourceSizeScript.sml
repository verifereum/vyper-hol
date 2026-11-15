Theory calldataSourceSize
Ancestors
  calldataSourceCorrespondence vyperCalldata vyperCalldataProps
  valueEncoding abiDecoderCoherence abiDecodeRanges
Libs wordsLib

Theorem tv_abi_static_memory_size:
  (!tv. ~tv_abi_dynamic tv ==>
    tv_abi_static_size tv = type_memory_size tv) /\
  (!tvs. ~tv_abi_dynamic_list tvs ==>
    tv_abi_static_size_list tvs = type_memory_size_list tvs) /\
  (!fs. ~tv_abi_dynamic_fields fs ==>
    tv_abi_static_size_fields fs = type_memory_size_fields fs)
Proof
  ho_match_mp_tac tv_abi_dynamic_ind >>
  simp[tv_abi_dynamic_def, tv_abi_static_size_def, type_memory_size_def]
QED

Theorem calldata_coherent_embedded_size:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv
Proof
  strip_tac >>
  drule calldata_coherent_dynamic >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, abi_member_head_size_def, tv_abi_size_def] >>
  metis_tac[tv_abi_static_memory_size]
QED
