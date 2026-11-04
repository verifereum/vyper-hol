(* Endpoint-facing metadata for encoding-equivalent source representatives. *)
Theory abiEncodeInputSupplier
Ancestors
  abiEncoderSourceAggregate abiCallerTupleLayout abiDecodeRanges exprLowering compileEnv

Theorem source_rep_static_memory:
  source_rep env ty ei ct /\ evaluate_type env ty = SOME tv /\
  ~is_dynamic ct ==>
  static_length ct = type_memory_size tv
Proof
  strip_tac >> drule_all source_rep_metadata >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by metis_tac[] >>
  drule_all abi_caller_static_memory >>
  gvs[abi_member_head_size_def]
QED

Theorem source_rep_compiler_layout:
  source_rep env ty ei ct /\ evaluate_type env ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type env ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type env ty) ==>
  abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size ct /\
  is_abi_dynamic ce.ce_struct_fields ty = is_dynamic ct /\
  (~is_dynamic ct ==> type_memory_bytes ce ty = static_length ct)
Proof
  strip_tac >> drule_all source_rep_metadata >> strip_tac >>
  simp[] >> metis_tac[source_rep_static_memory]
QED
