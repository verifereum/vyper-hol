(* Primitive source conversion linked to the word stored by the decoder. *)
Theory abiDecoderPrimitiveConversion
Ancestors
  abiBoundedLeafReflection abiDecoderCoherence abiDecoderWordTyped
  abiVyperAdmissible vyperTypeABI vyperABIRoundtrip vyperABIValid
  vyperABI valueEncoding valueEncodingProofs vyperTyping words list arithmetic compileEnv contractABI
  abiValidStatic byte rich_list

Theorem abi_decoder_primitive_reflected_conversion:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  32 <= LENGTH bs /\
  word_of_bytes T (0w:bytes32) (TAKE 32 bs) = w /\
  abi_decoder_clamp_valid clamp w ==>
  ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
      value_has_type tv v /\ typed_val_to_w256 tv v = w /\
      vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
      abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)` by
    (irule abi_decoder_primitive_reflect >> metis_tac[]) >>
  drule abi_vyper_admissible_convert >> strip_tac >>
  `evaluate_type env ty = SOME tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `value_has_type tv v` by metis_tac[cj 1 abi_to_vyper_well_typed] >>
  qexists `v` >> simp[] >>
  drule_all abi_decoder_primitive_cases >> strip_tac
  >- (gvs[] >> Cases_on `bt` >>
      gvs[is_word_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
        abi_to_vyper_def, dec_def, dec_number_def, check_IntV_def,
        typed_val_to_w256_def, val_to_w256_def, AllCaseEqs()]
      >- (Cases_on `w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) = 1` >>
          simp[] >>
          `w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) = 0 \/
           w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) = 1` by decide_tac >>
          metis_tac[n2w_w2n])
      >- (Cases_on `b` >> gvs[is_word_type_def, vyper_base_to_abi_type_def,
            abi_to_vyper_def, dec_def, typed_val_to_w256_def, AllCaseEqs()] >>
          `valid_enc (Bytes (SOME n)) bs` by
            fs[vyper_decode_valid_enc_def, valid_enc_def] >>
          drule_all abi_valid_fixed_bytes_prefix >>
          simp[enc_def, dec_def, word_of_bytes_be_def, PAD_RIGHT,
            TAKE_TAKE_MIN, MIN_DEF, LENGTH_TAKE_EQ, GSYM REPLICATE_GENLIST]) >>
      simp[GSYM word_to_bytes_w2w_address, word_of_bytes_be_def,
        vfmTypesTheory.word_to_bytes_word_of_bytes_256, w2w_n2w] >>
      fs[vyperValueTheory.within_int_bound_def, integer_wordTheory.i2w_def] >>
      simp[fcpLib.INDEX_CONV ``dimindex(:160)``, bitTheory.BITS_THM,
        MOD_EQ_0, LESS_MOD, n2w_w2n]) >>
  gvs[vyper_to_abi_type_def, abi_to_vyper_def, dec_def, dec_number_def,
    typed_val_to_w256_def, val_to_w256_def, AllCaseEqs()]
QED
