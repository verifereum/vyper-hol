(* Close the source-valid recursive execution API for prefix-reconstructible
   values. This includes all static ABI types and static-element dynamic arrays. *)
Theory abiDecoderValidPrefix
Ancestors
  abiDecoderValidContract abiDecoderCoherentCorrect abiDecoderArrayBody abiDecoderAllocation
  abiDecoderReentry abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  vyperABIValid abiValidStatic abiDecodeRanges compileEnv valueEncoding vyperABI contractABI venomState words
  list arithmetic

Theorem abi_decoder_valid_correct_prefix:
  (!bs. vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
     (is_dynamic (vyper_to_abi_type env ty) \/
       static_length (vyper_to_abi_type env ty) <= LENGTH bs) ==>
     LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)) <= LENGTH bs /\
     TAKE (LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs))) bs =
       enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)) ==>
  abi_decoder_valid_correct ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN ``vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   (is_dynamic (vyper_to_abi_type env ty) \/
     static_length (vyper_to_abi_type env ty) <= LENGTH bs)`` assume_tac
  >- fs[abi_decoder_valid_pre_def, Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"] >>
  qpat_x_assum `!bs. _` (qspec_then `bs` mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_reservation start.cs_next_id last b cap initial` by
    (drule_all abi_decoder_budget_child_reservation >> simp[]) >>
  drule_all abi_decoder_valid_pre_prefix >> strip_tac >>
  mp_tac (Q.INST [`av` |-> `dec (vyper_to_abi_type env ty) bs`] abi_decoder_decode) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_correct_static:
  ~is_dynamic (vyper_to_abi_type env ty) ==> abi_decoder_valid_correct ce env sf ty tv
Proof
  strip_tac >> irule abi_decoder_valid_correct_prefix >> rpt strip_tac >>
  `static_length (vyper_to_abi_type env ty) <= LENGTH bs` by
    fs[] >>
  `valid_enc (vyper_to_abi_type env ty) bs` by
    (irule vyper_decode_valid_enc_static >> simp[]) >>
  drule abi_static_prefix_static >> simp_tac bool_ss [abi_static_prefix_def] >>
  disch_then (qspec_then `bs` mp_tac) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE_MIN, Excl "dec_def", Excl "vyper_decode_valid_enc_def"]
QED

Theorem abi_decoder_valid_correct_static_array:
  vyper_to_abi_type env ty = Array NONE at /\ ~is_dynamic at ==>
  abi_decoder_valid_correct ce env sf ty tv
Proof
  strip_tac >> irule abi_decoder_valid_correct_prefix >> rpt strip_tac >>
  fs[Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"] >>
  `vyper_decode_valid_enc (Array NONE at) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ _` mp_tac >> asm_simp_tac bool_ss []) >>
  `valid_enc (Array NONE at) bs` by
    (qpat_x_assum `vyper_decode_valid_enc (Array NONE at) bs` mp_tac >>
     simp_tac bool_ss [Once vyper_decode_valid_enc_def, Once valid_enc_def, LET_THM] >>
     strip_tac >> gvs[] >>
     irule (cj 2 vyper_decode_valid_enc_static_mutual) >> simp[]) >>
  drule_all abi_valid_static_array_prefix >> simp[]
QED
