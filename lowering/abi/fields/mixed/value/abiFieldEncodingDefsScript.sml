(* TOP-LEVEL: pure field encodings connect actual compiler metadata, typed
   packed values and source ABI conversion. No memory or execution is assumed. *)
Theory abiFieldEncodingDefs
Ancestors
  abiFieldValueDefs abiFieldTypeMetadata abiFieldDefs vyperABI contractABI list

Definition abi_field_encoding_def:
  abi_field_encoding tenv sfields cenv ty tv v av row <=>
    abi_field_type_row sfields cenv ty row /\ abi_field_value tenv row tv v /\
    vyper_to_abi tenv ty v = SOME av /\
    abi_field_output row = (is_dynamic (vyper_to_abi_type tenv ty), enc (vyper_to_abi_type tenv ty) av)
End

Definition abi_field_encodings_def:
  (abi_field_encodings tenv sfields cenv [] [] [] [] [] <=> T) /\
  (abi_field_encodings tenv sfields cenv (ty::tys) (tv::tvs) (v::vs) (av::avs) (row::rows) <=>
    abi_field_encoding tenv sfields cenv ty tv v av row /\
    abi_field_encodings tenv sfields cenv tys tvs vs avs rows) /\
  (abi_field_encodings tenv sfields cenv _ _ _ _ _ <=> F)
End
