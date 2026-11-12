Theory abiDecodePtrScalarRejectFacts
Ancestors
  abiDecodePtrRejectChecks supportedTypes typedCopyMetadata vyperABIValid
  vyperTypeABI entryDecodeProps abiEncoder vyperABI contractABI
  valueEncoding vyperValue compileEnv stmtSimLogDataInput venomMemProps
  abiCanonicalHeadSize abiDecoderClamp words list arithmetic

Theorem abi_decode_supported_word_clamp_valid:
  supported_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  32 <= LENGTH bs /\ word_to_bytes (w:bytes32) T = TAKE 32 bs /\
  abi_clamp_ok clamp w ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs
Proof
  strip_tac >>
  `is_word_type ty` by metis_tac[supported_word_type_is_word] >>
  Cases_on `ty` >> gvs[supported_word_type_def] >>
  rename1 `BaseT bt` >>
  `evaluate_type env (BaseT bt) = SOME (BaseTV bt)` by
    (Cases_on `bt` >>
     gvs[supported_word_type_def, supported_int_width_def, evaluate_type_def,
         is_word_type_def, AllCaseEqs()] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[supported_word_type_def, evaluate_type_def]) >>
  mp_tac (Q.SPECL [`env`, `sf`, `ce`, `BaseT bt`]
    word_arg_clamp_inverse_selected) >>
  simp[] >> disch_then (qspec_then `w` strip_assume_tac) >>
  qpat_x_assum `abi_clamp_ok clamp w ==> _`
    (fn th => mp_tac th) >> impl_tac >- simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  drule_all log_word_abi_type >> strip_tac >>
  `valid_enc (vyper_to_abi_type env (BaseT bt))
     (enc (vyper_to_abi_type env (BaseT bt)) av ++ DROP 32 bs)` by
    (irule (cj 1 enc_valid) >> simp[dimword_def]) >>
  drule valid_enc_vyper_decode_valid_enc >>
  gvs[] >> simp[TAKE_DROP]
QED

Theorem abi_decode_supported_word_invalid_clamp:
  supported_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  32 <= LENGTH bs /\ word_to_bytes (w:bytes32) T = TAKE 32 bs /\
  ~vyper_decode_valid_enc (vyper_to_abi_type env ty) bs ==>
  ~abi_clamp_ok clamp w
Proof
  metis_tac[abi_decode_supported_word_clamp_valid]
QED

Theorem abi_decode_physical_word_invalid_clamp:
  supported_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decode_source_opcode opc /\ a < dimword(:256) /\
  32 <= LENGTH bs /\
  mem_bytes_at a (LENGTH bs) (abi_decode_source opc s) = bs /\
  ~vyper_decode_valid_enc (vyper_to_abi_type env ty) bs ==>
  ~abi_clamp_ok clamp (abi_decode_load opc (n2w a : bytes32) s)
Proof
  strip_tac >> irule abi_decode_supported_word_invalid_clamp >>
  qexistsl_tac [`bs`, `ce`, `env`, `sf`, `ty`] >>
  simp[] >>
  `mem_bytes_at a 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (mp_tac (Q.SPECL [`a`, `0`, `32`, `LENGTH (bs:word8 list)`, `abi_decode_source opc s`]
       mem_bytes_at_window) >> simp[]) >>
  simp[abi_decode_load_bytes] >> irule word_bytes_roundtrip_256 >> simp[]
QED
