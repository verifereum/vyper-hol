(* Domain audit: successful source conversion is weaker than plan applicability. *)
Theory exprSimAbiEncodePlanDomain
Ancestors
  exprSimAbiEncodePlanTranslation abiEncoderSourceAggregate vyperTypeValues
  allocLimits vyperTypeSystem vyperABI exprLowering valueEncoding compileEnv
  abiEncoderProps abiEncoderOpenInput abiEncoderInput contractABI vyperValue

Theorem abi_encode_none_source_domain:
  evaluate_type E NoneT = SOME NoneTV /\
  vyper_to_abi E NoneT NoneV = SOME (ListV []) /\
  ~assignable_type E NoneT /\
  type_to_abi_enc_info sf ce NoneT = AbiComplex []
Proof
  simp[evaluate_type_NoneT, vyper_to_abi_def, assignable_type_def,
       type_to_abi_enc_info_def]
QED

Theorem abi_encode_none_compiled_plan_excluded:
  ~abi_enc_plan E NoneT (type_to_abi_enc_info sf ce NoneT)
Proof
  simp[type_to_abi_enc_info_def, Once abi_enc_plan_cases, is_word_type_def]
QED

Theorem abi_encode_none_copy_plan:
  abi_enc_plan E NoneT (AbiCopy 0)
Proof
  simp[Once abi_enc_plan_cases, vyper_to_abi_type_def, is_dynamic_def,
       type_memory_size_def]
QED

Theorem abi_encode_empty_tuple_compiled_plan:
  abi_enc_plan E (TupleT []) (type_to_abi_enc_info sf ce (TupleT []))
Proof
  simp[type_to_abi_enc_info_def, is_abi_dynamic_def, type_memory_bytes_def] >>
  simp[Once abi_enc_plan_cases, vyper_to_abi_type_def, is_dynamic_def,
       evaluate_type_def, type_memory_size_def, type_slot_size_def]
QED

(* The open representation interface does cover the descriptor that the
   stricter plan relation excludes. No change to encoder definitions is needed. *)
Theorem abi_encode_none_open_input:
  abi_encoder_open_input (type_to_abi_enc_info sf ce NoneT)
    (Tuple []) (ListV []) sb cap mem
Proof
  simp[type_to_abi_enc_info_def, abi_encoder_open_complex_iff,
       abi_encoder_tuple_type_def, abi_encoder_member_span_def]
QED

Theorem abi_encode_none_source_rep:
  source_rep E NoneT (type_to_abi_enc_info sf ce NoneT) (Tuple [])
Proof
  rw[source_rep_def, vyper_to_abi_type_def] >>
  gvs[vyper_to_abi_def, AllCaseEqs()] >>
  qexists_tac `ListV []` >> simp[abi_encode_none_open_input]
QED

Theorem abi_encode_none_static_arg_domain:
  well_typed_type_builtin_args (AbiEncode ensure NONE) (TupleT [NoneT]) [NoneT]
Proof
  simp[well_typed_type_builtin_args_def]
QED
