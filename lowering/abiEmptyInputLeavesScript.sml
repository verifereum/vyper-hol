(* Establish default leaf encoder inputs from real initialized memory windows. *)
Theory abiEmptyInputLeaves
Ancestors
  abiEmptyInputTransport abiEmptyDefault abiDecoderLayout abiDecoderCoherence
  abiEncoderInput compileEnv exprLowering valueEncoding vyperABI
  contractABI words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_INPUT_LEAVES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty leaf input not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyInputLeaves");
