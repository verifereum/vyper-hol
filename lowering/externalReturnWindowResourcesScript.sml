Theory externalReturnWindowResources
Ancestors
  abiEncoderSourceProducer abiEncoderWindow abiEncoderAdmissible
  retAbiPlanProps vyperABIValid

(* The representative encoding may use a different ABI type but has exactly
   the same bytes, so its destination bound is the source ABI size bound. *)
Theorem return_plan_nominal_source_window:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v p mem ==>
  ?at rv. abi_encoder_window_input ei at rv p (type_memory_size tv) mem /\
    enc at rv = enc (vyper_to_abi_type env ty) av /\
    LENGTH (enc at rv) <= vyper_abi_size_bound env ty
Proof
  strip_tac >> drule_all abi_encoder_source_window >> strip_tac >>
  drule_all abi_encoder_open_input_window >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_enc_le_size_bound) >> strip_tac >>
  qexistsl_tac [`ct`, `rv`] >> simp[]
QED

Theorem return_plan_encoder_admissible:
  abi_encoder_admissible (update_cenv_ret_abi ce ty).ce_ret_enc_info
Proof
  simp[compileVyperTheory.update_cenv_ret_abi_def] >>
  IF_CASES_TAC >> simp[abi_encoder_admissible_def,
                       abi_encoder_translation_admissible]
QED

(* Singleton metadata may retain the return type's larger stride.  Only the
   actual bytes are read, independently of that nominal member stride. *)
Theorem return_bytes_window_retarget:
  abi_encoder_window_input (AbiBytestring n) at (BytesV bs) p cap mem /\
  LENGTH bs <= maxlen /\ 32 + LENGTH bs <= mem_sz ==>
  abi_encoder_window_input
    (AbiComplex [(AbiBytestring maxlen,32,mem_sz,T)])
    (Tuple [at]) (ListV [BytesV bs]) p (32 + LENGTH bs) mem
Proof
  simp[abi_encoder_window_bytes_iff] >> strip_tac >>
  metis_tac[abi_encoder_window_singleton_bytes, arithmeticTheory.ADD_COMM]
QED
