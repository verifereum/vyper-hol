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

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed pure source/compiler field encodings: " ^ name)
  end) (DB.thms "abiFieldEncodingDefs")
