(* Transfer pure zero-memory encoder inputs to an actually initialized buffer.
   Count-only producers need only their initialized first word. *)
Theory abiEmptyInputTransport
Ancestors
  abiEncoderInput abiEncoderInputLayout abiEncoderInputFrame abiStaticPrimitiveProps
  valueEncoding valueEncodingProofs contractABI words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_INPUT_TRANSPORT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty input transport not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyInputTransport");
