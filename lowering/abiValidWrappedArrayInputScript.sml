(* Successful wrapped dynamic-array source decoding establishes the logical
   singleton input, including noncanonical offsets and trailing child bytes. *)
Theory abiValidWrappedArrayInput
Ancestors
  abiValidSingletonPrefixInput abiValidSingletonArray abiValidWrappedSourceValue
  abiValidDecodedMetadata abiValidStaticArray abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_valid_singleton_prefix_pre_from_conversion:
  abi_decoder_coherent ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty) /\
  valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\ abi_head_word bs <= LENGTH bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) = SOME v /\
  LENGTH (enc (vyper_to_abi_type env ty)
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs))) <=
      LENGTH (DROP (abi_head_word bs) bs) /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty)
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)))) (DROP (abi_head_word bs) bs) =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_valid_singleton_prefix_pre ce env sf ty tv bs
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) v
    st src dst opc hi sb d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `dec (Tuple [vyper_to_abi_type env ty]) bs =
    ListV [dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)]` by
    (irule abi_dynamic_singleton_value >> asm_simp_tac bool_ss []) >>
  drule_all abi_valid_singleton_dynamic_decode >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  asm_simp_tac bool_ss [abi_valid_singleton_prefix_pre_def]
QED

Theorem abi_valid_wrapped_array_prefix_pre:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  evaluate_abi_decode env (TupleT [ArrayT ty (Dynamic maxn)]) bs = INL (ArrayV (TupleV [v])) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_valid_singleton_prefix_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) bs
    (dec (Array NONE (vyper_to_abi_type env ty)) (DROP (abi_head_word bs) bs)) v
    st src dst opc hi sb d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic maxn)))` by
    simp[vyper_to_abi_type_def] >>
  drule_all abi_valid_dynamic_singleton_source >> strip_tac >>
  `dec (Tuple [Array NONE (vyper_to_abi_type env ty)]) bs =
    ListV [dec (Array NONE (vyper_to_abi_type env ty)) (DROP (abi_head_word bs) bs)]` by
    (irule abi_dynamic_singleton_value >> simp[]) >>
  `valid_enc (Tuple [Array NONE (vyper_to_abi_type env ty)]) bs` by
    fs[vyper_to_abi_type_def, Excl "valid_enc_def"] >>
  drule_all abi_valid_singleton_array_decode >> strip_tac >>
  drule_all abi_valid_static_array_prefix >> strip_tac >>
  `abi_head_word bs <= LENGTH bs` by decide_tac >>
  mp_tac (Q.INST [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`]
    abi_valid_singleton_prefix_pre_from_conversion) >>
  asm_simp_tac bool_ss [vyper_to_abi_type_def, is_dynamic_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_WRAPPED_ARRAY_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid wrapped array input not kernel closed: " ^ n)
  end) (DB.thms "abiValidWrappedArrayInput");
