(* Singleton ABI wrappers share the child's source window. *)
Theory extRetAbiWrappedSourcePtr
Ancestors
  extRetAbiSourceInputPtr abiEncoderInput abiDecodeRanges contractABI compileEnv
  bodyPtrDefs valueEncoding words list

Theorem abi_encoder_input_singleton:
  abi_encoder_input ei at av sb cap mem ==>
  abi_encoder_input
    (AbiComplex [(ei, abi_member_head_size at, cap, is_dynamic at)])
    (Tuple [at]) (contractABI$ListV [av]) sb cap mem
Proof
  strip_tac >>
  drule abi_encoder_input_typed >> strip_tac >>
  simp[abi_encoder_complex_input_iff] >>
  qexists_tac `[at]` >>
  simp[abi_encoder_tuple_type_def, has_type_def,
       abi_encoder_member_span_def] >>
  rpt strip_tac >>
  `i = 0` by decide_tac >> gvs[abi_encoder_member_span_def]
QED

Theorem robust_abi_encoder_input_singleton:
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input ei at av sb cap mem') ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input
      (AbiComplex [(ei, abi_member_head_size at, cap, is_dynamic at)])
      (Tuple [at]) (contractABI$ListV [av]) sb cap mem'
Proof
  rpt strip_tac >> irule abi_encoder_input_singleton >>
  first_x_assum irule >> simp[]
QED

Theorem ptr_val_ok_bytes_wrapped_abi_input:
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (vyperValue$BytesV bs) op G tn s /\
  eval_operand op s = SOME w /\
  value_has_type (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  n < dimword(:256) ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input
      (AbiComplex [(AbiBytestring n,32,
        type_memory_size (BaseTV (BytesT (Dynamic n))),T)])
      (Tuple [Bytes NONE]) (contractABI$ListV [contractABI$BytesV bs])
      (w2n w) (type_memory_size (BaseTV (BytesT (Dynamic n)))) mem'
Proof
  rpt strip_tac >> drule_all ptr_val_ok_bytes_abi_input >>
  strip_tac >> drule abi_encoder_input_singleton >>
  simp[abi_member_head_size_def, is_dynamic_def]
QED

Theorem ptr_val_ok_string_wrapped_abi_input:
  ptr_val_ok cx (BaseT (StringT n)) (StringV text) op G tn s /\
  eval_operand op s = SOME w /\
  value_has_type (BaseTV (StringT n)) (StringV text) /\
  val_wf (BaseTV (StringT n)) (StringV text) /\
  n < dimword(:256) ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input
      (AbiComplex [(AbiBytestring n,32,
        type_memory_size (BaseTV (StringT n)),T)])
      (Tuple [String])
      (contractABI$ListV [contractABI$BytesV (MAP (n2w o ORD) text)])
      (w2n w) (type_memory_size (BaseTV (StringT n))) mem'
Proof
  rpt strip_tac >> drule_all ptr_val_ok_string_abi_input >>
  strip_tac >> drule abi_encoder_input_singleton >>
  simp[abi_member_head_size_def, is_dynamic_def]
QED
