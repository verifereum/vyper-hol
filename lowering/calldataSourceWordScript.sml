Theory calldataSourceWord
Ancestors
  calldataSourceCorrespondence calldataWordProps entryDecodeProps
  abiDecoderCoherence exprLowering vyperCalldata vyperTyping
  valueEncodingDefs compileEnv words integer_word list arithmetic

Theorem calldata_coherent_word_value:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty ==>
  (cd_word_value tv w = SOME x <=>
   value_has_type tv x /\ typed_val_to_w256 tv x = w)
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  irule cd_word_value_encoding >> metis_tac[]
QED

Theorem calldata_coherent_selected_flags[local]:
  abi_decoder_coherent ce env sf ty tv ==>
  !nsid. ty = FlagT nsid ==> ?m.
    FLOOKUP env nsid = SOME (FlagArgs m) /\
    ce.ce_flag_n_members (nsid_to_string nsid) = m
Proof
  rpt strip_tac >> gvs[abi_decoder_coherent_flag_iff] >> metis_tac[]
QED

Theorem calldata_coherent_word_accepts:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  (cd_word_value tv w <> NONE <=> abi_clamp_ok clamp w)
Proof
  strip_tac >>
  drule calldata_coherent_selected_flags >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  eq_tac
  >- (Cases_on `cd_word_value tv w` >> simp[] >>
      drule_all calldata_coherent_word_value >> simp[] >> strip_tac >>
      `abi_clamp_ok
        (case type_to_abi_dec_info sf ce ty of
           DecPrimWord c => c | _ => NoClamp)
        (typed_val_to_w256 tv x)` by
        (irule word_arg_clamp_ok_selected >> simp[] >>
         metis_tac[]) >> gvs[]) >>
  strip_tac >>
  `?x. value_has_type tv x /\ typed_val_to_w256 tv x = w` by
    (qspecl_then [`env`, `sf`, `ce`, `ty`] mp_tac
       word_arg_clamp_inverse_selected >> simp[]) >>
  drule_all calldata_coherent_word_value >>
  disch_then (qspecl_then [`x`, `w`] mp_tac) >> simp[] >>
  Cases_on `cd_word_value tv w` >> simp[]
QED

Theorem calldata_coherent_word_rejects:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  (cd_word_value tv w = NONE <=> ~abi_clamp_ok clamp w)
Proof
  strip_tac >> drule_all calldata_coherent_word_accepts >> metis_tac[]
QED
