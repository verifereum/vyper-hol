Theory abiEmptyInput
Ancestors
  abiEncoderInput abiEncoderInputFrame abiStaticPrimitiveProps valueEncoding valueEncodingProofs
  contractABI words list arithmetic abiEmptyDefault abiDecoderLayout abiDecoderCoherence
  compileEnv exprLowering vyperABI

(* ===== Transport ===== *)

(* Transfer pure zero-memory encoder inputs to an actually initialized buffer.
   Count-only producers need only their initialized first word. *)

Theorem abi_empty_memory_observation:
  mem_bytes_at p sz [] = REPLICATE sz 0w /\ mem_word_at p [] = 0w
Proof
  simp[mem_bytes_at_def, mem_word_at_def, TAKE_LENGTH_TOO_LONG,
    word_of_bytes_replicate_zero]
QED

Theorem abi_empty_count_word:
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==> mem_word_at p mem = 0w
Proof
  simp[mem_word_at_bytes, word_of_bytes_replicate_zero]
QED

Theorem abi_empty_input_relocate:
  abi_encoder_input ei at av 0 cap [] /\
  mem_bytes_at p cap mem = REPLICATE cap 0w ==>
  abi_encoder_input ei at av p cap mem
Proof
  strip_tac >> drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`p`, `mem`] mp_tac) >>
  simp[abi_empty_memory_observation]
QED

Theorem abi_empty_input_zero_address:
  abi_encoder_input ei at av 0 cap [] ==> abi_encoder_input ei at av p cap []
Proof
  strip_tac >> irule abi_empty_input_relocate >> simp[abi_empty_memory_observation]
QED

Theorem abi_empty_bytes_input:
  (at = Bytes NONE \/ at = String) /\ 32 <= cap /\ mem_word_at p mem = 0w ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV []) p cap mem
Proof
  rw[abi_encoder_input_bytes_iff, has_type_def, valid_length_def,
    mem_bytes_at_def, dimword_def] >>
  simp[has_type_def, valid_bytes_bound_def, valid_length_def, dimword_def]
QED

Theorem abi_empty_array_input:
  abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
  32 <= cap /\ mem_word_at p mem = 0w ==>
  abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) (Array NONE ct) (ListV []) p cap mem
Proof
  simp[abi_encoder_array_input_iff, has_type_def, valid_length_def, dimword_def]
QED

(* ===== Leaves ===== *)

(* Establish default leaf encoder inputs from real initialized memory windows. *)

Theorem abi_empty_coherent_static_input:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  mem_bytes_at p (type_memory_bytes ce ty) mem = REPLICATE (type_memory_bytes ce ty) 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) p (type_memory_bytes ce ty) mem
Proof
  strip_tac >> drule_all abi_decoder_coherent_static >> strip_tac >>
  irule abi_empty_static_input >> simp[]
QED

Theorem abi_empty_bytestring_inputs:
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (BytesT (Dynamic n))))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n))))
    (default_to_abi (BaseTV (BytesT (Dynamic n)))) p
    (type_memory_bytes ce (BaseT (BytesT (Dynamic n)))) mem /\
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (StringT m)))
    (vyper_to_abi_type env (BaseT (StringT m)))
    (default_to_abi (BaseTV (StringT m))) p
    (type_memory_bytes ce (BaseT (StringT m))) mem
Proof
  strip_tac >> drule abi_empty_count_word >> strip_tac >>
  simp_tac bool_ss [type_to_abi_enc_info_def, vyper_to_abi_type_def,
    default_to_abi_def, type_memory_bytes_def] >>
  conj_tac >> irule abi_empty_bytes_input >> simp[]
QED

Theorem abi_empty_dynamic_array_input:
  abi_decoder_header ce env ty tv /\
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (ArrayT ty (Dynamic n)))
    (vyper_to_abi_type env (ArrayT ty (Dynamic n)))
    (default_to_abi (ArrayTV tv (Dynamic n))) p
    (type_memory_bytes ce (ArrayT ty (Dynamic n))) mem
Proof
  strip_tac >> drule abi_empty_count_word >> strip_tac >>
  simp_tac bool_ss [type_to_abi_enc_info_def, vyper_to_abi_type_def,
    default_to_abi_def, type_memory_bytes_def] >>
  irule abi_empty_array_input >> gvs[abi_decoder_header_def]
QED
