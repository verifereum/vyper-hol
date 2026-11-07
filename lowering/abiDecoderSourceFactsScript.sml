(* Source and checker facts for arbitrary primitive and bytestring decoder outcomes. *)
Theory abiDecoderSourceFacts
Ancestors
  abiDecoderClampOutcome vyperTypeSystem vyperABI contractABI
  exprLowering vyperValue list rich_list arithmetic words byte

Theorem abi_decode_scalar_descriptors:
  type_to_abi_dec_info sf ce (BaseT BoolT) = DecPrimWord BoolClamp /\
  type_to_abi_dec_info sf ce (BaseT AddressT) = DecPrimWord (IntClamp 160 F) /\
  type_to_abi_dec_info sf ce (BaseT DecimalT) = DecPrimWord (IntClamp 168 T) /\
  type_to_abi_dec_info sf ce (BaseT (UintT n)) =
    DecPrimWord (if n = 256 then NoClamp else IntClamp n F) /\
  type_to_abi_dec_info sf ce (BaseT (IntT n)) =
    DecPrimWord (if n = 256 then NoClamp else IntClamp n T) /\
  type_to_abi_dec_info sf ce (BaseT (BytesT (Fixed m))) =
    DecPrimWord (if m = 32 then NoClamp else BytesMClamp m) /\
  type_to_abi_dec_info sf ce (BaseT (BytesT (Dynamic m))) = DecBytestring m /\
  type_to_abi_dec_info sf ce (BaseT (StringT m)) = DecBytestring m /\
  type_to_abi_dec_info sf ce (FlagT nsid) =
    DecPrimWord (if ce.ce_flag_n_members (nsid_to_string nsid) = 256 then NoClamp
      else IntClamp (ce.ce_flag_n_members (nsid_to_string nsid)) F)
Proof
  simp[type_to_abi_dec_info_def, type_to_abi_clamp_def]
QED

Theorem abi_decode_word_validation:
  LENGTH (bs:byte list) = 32 ==>
  (vyper_decode_valid_enc (Uint n) bs <=>
    valid_int_bound n /\ w2n (word_of_bytes T (0w:bytes32) bs) < 2 ** n) /\
  (vyper_decode_valid_enc (Int n) bs <=>
    valid_int_bound n /\ int_bits_bound (w2i (word_of_bytes T (0w:bytes32) bs)) n) /\
  (vyper_decode_valid_enc Address bs <=>
    w2n (word_of_bytes T (0w:bytes32) bs) < 2 ** 160) /\
  (vyper_decode_valid_enc Bool bs <=>
    w2n (word_of_bytes T (0w:bytes32) bs) < 2) /\
  (vyper_decode_valid_enc (Bytes (SOME m)) bs <=>
    0 < m /\ m <= 32 /\ EVERY ((=) 0w) (DROP m bs))
Proof
  strip_tac >> simp[vyper_decode_valid_enc_def, dec_number_def,
    has_type_def, valid_bytes_bound_def, TAKE_LENGTH_TOO_LONG] >>
  metis_tac[]
QED

Theorem abi_decode_word_dec:
  LENGTH (bs:byte list) = 32 ==>
  dec (Uint n) bs = NumV (w2n (word_of_bytes T (0w:bytes32) bs)) /\
  dec (Int n) bs = contractABI$IntV (w2i (word_of_bytes T (0w:bytes32) bs)) /\
  dec Address bs = NumV (w2n (word_of_bytes T (0w:bytes32) bs)) /\
  dec Bool bs = NumV (w2n (word_of_bytes T (0w:bytes32) bs)) /\
  dec (Bytes (SOME m)) bs = contractABI$BytesV (TAKE m bs)
Proof
  simp[dec_def, dec_number_def, TAKE_LENGTH_TOO_LONG]
QED

Theorem abi_decode_checker_clamp_wf:
  assignable_type env (BaseT bt) /\ abi_decode_bytes_widths env (BaseT bt) ==>
  abi_decoder_clamp_wf (type_to_abi_clamp (BaseT bt))
Proof
  Cases_on `bt` >>
  simp[assignable_type_def, well_formed_type_def, evaluate_type_def,
    abi_decode_bytes_widths_def, type_to_abi_clamp_def,
    abi_decoder_clamp_wf_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rw[abi_decoder_clamp_wf_def] >>
  Cases_on `b` >> gvs[type_to_abi_clamp_def, AllCaseEqs()] >>
  rw[abi_decoder_clamp_wf_def]
QED

Theorem abi_decode_flag_conversion:
  FLOOKUP env nsid = SOME (FlagArgs m) ==>
  abi_to_vyper env (FlagT nsid) (NumV n) =
    (if m <= 256 /\ n < 2 ** m then SOME (FlagV (&n)) else NONE)
Proof
  simp[abi_to_vyper_def]
QED

Theorem abi_decode_bytestring_validation:
  32 <= LENGTH (bs:byte list) ==>
  (vyper_decode_valid_enc (Bytes NONE) bs <=>
    w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) <= LENGTH bs - 32) /\
  (vyper_decode_valid_enc String bs <=>
    w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) <= LENGTH bs - 32) /\
  dec (Bytes NONE) bs = contractABI$BytesV
    (TAKE (w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs))) (DROP 32 bs)) /\
  dec String bs = contractABI$BytesV
    (TAKE (w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs))) (DROP 32 bs))
Proof
  simp[vyper_decode_valid_enc_def, dec_def, dec_number_def,
       is_num_value_def, dest_NumV_def]
QED
