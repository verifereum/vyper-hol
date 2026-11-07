Theory ctorDeployMemoryRunMemEntryStrictProbe
Ancestors
  ctorSourceInputs abiDecoderCoherence vyperTypeSystem vyperABI
  vyperInterpreter vyperValue contractABI supportedTypes supportedDecls

(* Source assignability is weaker than strict ABI validity. This is a probe
   of the registration interface, not a counterexample to deployment. *)
Theorem ctor_zero_bytes_source_probe:
  assignable_type env (BaseT (BytesT (Fixed 0))) /\
  vyper_to_abi env (BaseT (BytesT (Fixed 0))) (vyperValue$BytesV []) =
    SOME (contractABI$BytesV []) /\
  ~has_type (Bytes (SOME 0)) (contractABI$BytesV [])
Proof
  simp[assignable_type_def, well_formed_type_def, evaluate_type_def,
       vyper_to_abi_def, vyper_to_abi_base_def,
       abi_decoder_zero_fixed_bytes_probe]
QED

(* Unlike assignability, the deployment support whitelist excludes bytes0. *)
Theorem ctor_zero_bytes_not_supported:
  ~supported_function_argument tops Deploy (BaseT (BytesT (Fixed 0)))
Proof
  simp[supported_function_argument_def, supported_value_type_def,
       supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED
