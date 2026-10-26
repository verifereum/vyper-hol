(* Source-success builtin input with physical scratch resources after output allocation. *)
Theory abiScratchDecodeInput
Ancestors
  abiScratchDecoderContract abiScratchFootprint abiBuiltinValidInput abiBuiltinSourceInput
  abiBuiltinDecodeSetup abiBuiltinAllocationState abiDecoderReadableTypes
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderAllocation
  abiDecodeRanges vyperABIValid vyperABI contractABI compileEnv valueEncoding
  valueEncodingProps venomState words list

Definition abi_scratch_decode_resources_def:
  abi_scratch_decode_resources st first last min_size max_size outsz cnt p d b cap s <=>
    min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
    p + 32 + cnt < dimword (:256) /\ d + outsz < dimword (:256) /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,outsz)) /\
    first <= abi_builtin_decode_output_site st min_size max_size + 2 /\
    let allocated = abi_builtin_allocate_state
      (abi_builtin_decode_output_site st min_size max_size) outsz s in
    abi_decoder_budget first last b cap allocated /\
    abi_footprint_disjoint d outsz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
    abi_footprint_disjoint (p + 32) cnt
      ((d,outsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated)
End

Definition abi_scratch_decode_pre_def:
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec (vyper_to_abi_type env ty) bs) v /\
    valid_enc (vyper_to_abi_type env ty) bs /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      static_length (vyper_to_abi_type env ty) <= LENGTH bs) /\
    val_in_memory (BaseTV (BytesT (Dynamic (LENGTH bs)))) (vyperValue$BytesV bs) p s.vs_memory /\
    eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
    abi_scratch_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
      (LENGTH bs) p d b cap s
End

Theorem abi_scratch_decode_source:
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s ==>
  mload p s = n2w (LENGTH bs) /\ mem_bytes_at (p + 32) (LENGTH bs) s.vs_memory = bs
Proof
  simp_tac bool_ss [abi_scratch_decode_pre_def] >> strip_tac >>
  fs[val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem abi_scratch_decode_pre_from_source:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_abi_decode env ty bs = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_scratch_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_source_metadata >> strip_tac >>
  drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  drule vyper_valid_enc_length_lower >> strip_tac >>
  asm_simp_tac bool_ss [abi_scratch_decode_pre_def] >>
  fs[vyper_valid_enc_def, val_in_memory_def, Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODE_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical builtin decoder input not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecodeInput");

