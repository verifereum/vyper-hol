(* Descriptor classification independent of decoder execution. *)
Theory abiDecoderBytestringCases
Ancestors
  abiDecoderCoherence abiEncoder exprLowering compileEnv
  vyperABI vyperTyping contractABI valueEncoding combin

Theorem abi_decoder_bytestring_cases:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !n. type_to_abi_dec_info sf ce ty = DecBytestring n ==>
  (ty = BaseT (BytesT (Dynamic n)) /\ tv = BaseTV (BytesT (Dynamic n))) \/
  (ty = BaseT (StringT n) /\ tv = BaseTV (StringT n))
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> Cases_on `bt` >>
      FIRST [(rename1 `BytesT bd` >> Cases_on `bd`), all_tac] >>
      simp[Once type_to_abi_dec_info_def])
  >- simp[Once type_to_abi_dec_info_def]
  >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
      simp[Once type_to_abi_dec_info_def])
  >- (rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def]) >>
  rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def]
QED
