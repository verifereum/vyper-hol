(* TOP-LEVEL: ABI format constraints and source-to-ABI typing predicates.
   Format constraints concern types only; values are checked by source typing. *)
Theory sourceAbiTypingDefs
Ancestors
  vyperABI vyperTyping contractABI list words

Definition abi_type_format_def:
  abi_type_format (Uint n) = valid_int_bound n /\
  abi_type_format (Int n) = valid_int_bound n /\
  abi_type_format Address = T /\
  abi_type_format Bool = T /\
  abi_type_format (Fixed n m) = valid_fixed_bounds n m /\
  abi_type_format (Ufixed n m) = valid_fixed_bounds n m /\
  abi_type_format (Bytes b) = valid_bytes_bound b /\
  abi_type_format String = T /\
  abi_type_format (Array b t) =
    (abi_type_format t /\ case b of NONE => T | SOME n => n < dimword(:256)) /\
  abi_type_format (Tuple ts) =
    (LENGTH ts < dimword(:256) /\ EVERY abi_type_format ts)
End

Definition source_abi_typed_def:
  source_abi_typed tv <=>
    !env ty v av.
      evaluate_type env ty = SOME tv /\ value_has_type tv v /\
      abi_type_format (vyper_to_abi_type env ty) /\
      vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av
End

Definition source_abi_types_typed_def:
  source_abi_types_typed tvs <=>
    !env tys vs avs.
      LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
      values_have_types tvs vs /\
      EVERY (abi_type_format o vyper_to_abi_type env) tys /\
      vyper_to_abi_list env tys vs = SOME avs ==>
      has_types (MAP (vyper_to_abi_type env) tys) avs
End
