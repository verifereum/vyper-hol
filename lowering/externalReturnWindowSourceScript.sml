(* The terminal consumes normalized typed windows; bytes/string need only
   their actual read windows, even under the declared singleton ABI stride. *)
Theory externalReturnWindowSource
Ancestors
  abiEncoderWindowSource abiEncoderSourceInvoke vyperLoweringCorrect
  abiEncoderAdmissible vyperABI vyperValue vyperTyping valueEncoding
  contractABI list arithmetic

Theorem return_abi_window_value:
  evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) ei /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= msz ==>
  ?av.
    vyper_to_abi (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then ArrayV (TupleV [v]) else v) = SOME av /\
    abi_encoder_admissible ei /\
    LENGTH (enc (vyper_to_abi_type (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)) av) <= msz /\
    return_bytes tops ret v
      (enc (vyper_to_abi_type (type_env tops)
        (if needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)
         then TupleT [ret] else ret)) av)
Proof
  strip_tac >> drule_all return_abi_value_package >>
  disch_then (qspec_then
    `needs_external_call_wrap ret /\
     is_dynamic (vyper_to_abi_type (type_env tops) ret)` strip_assume_tac) >>
  qexists_tac `av` >> gvs[] >>
  metis_tac[cj 1 abi_enc_plan_admissible, chosen_return_abi_bytes, LESS_EQ_TRANS]
QED

Theorem return_window_bytes_singleton:
  evaluate_type env (BaseT (BytesT (Dynamic n))) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem /\ sb + val_footprint tv v <= limit ==>
  abi_encoder_window_input
    (AbiComplex [(AbiBytestring n,32,type_memory_size tv,T)])
    (Tuple [Bytes NONE]) (ListV [BytesV bs]) sb (32 + LENGTH bs) mem /\
  sb + (32 + LENGTH bs) <= limit
Proof
  strip_tac >> conj_tac
  >- (irule abi_encoder_window_bytes_singleton_source >> metis_tac[]) >>
  gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def] >>
  metis_tac[abi_encoder_window_bytes_actual_bound, ADD_COMM]
QED

Theorem return_window_string_singleton:
  evaluate_type env (BaseT (StringT n)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (StringT n)) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem /\ sb + val_footprint tv v <= limit ==>
  abi_encoder_window_input
    (AbiComplex [(AbiBytestring n,32,type_memory_size tv,T)])
    (Tuple [String]) (ListV [BytesV bs]) sb (32 + LENGTH bs) mem /\
  sb + (32 + LENGTH bs) <= limit
Proof
  strip_tac >> conj_tac
  >- (irule abi_encoder_window_string_singleton_source >> metis_tac[]) >>
  gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def] >>
  metis_tac[abi_encoder_window_string_actual_bound, ADD_COMM]
QED
