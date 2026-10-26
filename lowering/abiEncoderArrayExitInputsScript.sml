(* The complete source relation supplies the real exit reload and its semantic length. *)
Theory abiEncoderArrayExitInputs
Ancestors
  abiEncoderArrayMemory abiEncoderArrayLayout abiEncoderInputLayout abiEncoderChildInputs
  abiEncoderInput abiEncoderMemory abiDecodeRanges abiDecoderContract
  compileEnv valueEncoding valueEncodingProps contractABI venomState words list arithmetic

Theorem abi_encoder_count_word_length:
  !payload:num. 32 <= payload ==> 32+(payload-32) = payload
Proof
  decide_tac
QED

Theorem abi_encoder_array_exit_inputs:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap j s ==>
  has_type (Array NONE ty) (ListV avs) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w (LENGTH avs) /\
  asz = abi_member_head_size ty /\ active = is_dynamic ty /\ sb < dimword (:256) /\
  32 <= LENGTH (enc (Array NONE ty) (ListV avs))
Proof
  strip_tac >> drule abi_encoder_array_memory_typed >> strip_tac >>
  drule abi_encoder_array_encoding_bound >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  gvs[mem_word_at_eq_mload] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_EXIT_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array exit inputs not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayExitInputs");
