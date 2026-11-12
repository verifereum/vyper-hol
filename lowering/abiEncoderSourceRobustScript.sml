(* Choose ABI representatives before varying unread or tainted memory. *)
Theory abiEncoderSourceRobust
Ancestors
  abiEncoderLiveSource abiEncoderSourceProducer abiEncoderSourceAggregate
  abiEncoderSourceWindow abiEncoderWindow abiEncoderOpenInput bodyPtrDefs
  vyperABI vyperABIValid vyperTyping vyperValue valueEncoding loweringPosts
  contractABI list arithmetic

Theorem abi_encoder_source_window_robust:
  abi_enc_plan env ty ei /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==>
    val_in_memory tv v sb mem) ==>
  ?ct rv.
    contractABI$enc ct rv =
      contractABI$enc (vyper_to_abi_type env ty) av /\
    LENGTH (contractABI$enc ct rv) <= vyper_abi_size_bound env ty /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_window_input ei ct rv sb (val_footprint tv v) mem
Proof
  cheat (* SEQ-4390 LOCAL STUB: SEQ-4024 producer *)
QED
