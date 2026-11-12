(* Runtime pointer representations supply robust encoder source inputs. *)
Theory extRetAbiSourceInputPtr
Ancestors
  bodyPtrDefs representationCleanPtr abiEncoderSourceCorrect abiEncoderInput
  exprLowering compileEnv vyperABI vyperValue valueEncoding vyperTyping words list vyperArith vfmConstants

Theorem ptr_val_ok_bytes_abi_input:
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (vyperValue$BytesV bs) op G tn s /\
  eval_operand op s = SOME w /\
  value_has_type (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  n < dimword(:256) ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring n) (Bytes NONE) (contractABI$BytesV bs)
      (w2n w) (type_memory_size (BaseTV (BytesT (Dynamic n)))) mem'
Proof
  rpt strip_tac >>
  `1 + word_size n <= dimword(:256)` by
    (Cases_on `n = 0` >- simp[word_size_def] >>
     `word_size n <= n` by (irule word_size_le >> decide_tac) >> decide_tac) >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def, evaluate_type_def, type_slot_size_def] >>
  strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) (w2n w) mem'` by metis_tac[] >>
  drule_all abi_encoder_bytes_source_input >>
  simp[type_to_abi_enc_info_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def]
QED

Theorem ptr_val_ok_string_abi_input:
  ptr_val_ok cx (BaseT (StringT n)) (StringV text) op G tn s /\
  eval_operand op s = SOME w /\
  value_has_type (BaseTV (StringT n)) (StringV text) /\
  val_wf (BaseTV (StringT n)) (StringV text) /\
  n < dimword(:256) ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring n) String
      (contractABI$BytesV (MAP (n2w o ORD) text))
      (w2n w) (type_memory_size (BaseTV (StringT n))) mem'
Proof
  rpt strip_tac >>
  `1 + word_size n <= dimword(:256)` by
    (Cases_on `n = 0` >- simp[word_size_def] >>
     `word_size n <= n` by (irule word_size_le >> decide_tac) >> decide_tac) >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def, evaluate_type_def, type_slot_size_def] >>
  strip_tac >>
  `val_in_memory (BaseTV (StringT n)) (StringV text) (w2n w) mem'` by metis_tac[] >>
  drule_all abi_encoder_string_source_input >>
  simp[type_to_abi_enc_info_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def]
QED
