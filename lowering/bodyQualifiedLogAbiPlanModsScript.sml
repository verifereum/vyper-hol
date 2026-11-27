(* Qualified linked Log ABI plan input: recursion is bounded by evaluated type size,
   so no global unqualified-struct namespace premise is needed. *)
Theory bodyQualifiedLogAbiPlanMods
Ancestors
  exprSimAbiEncodePlanTranslation abiTypeBoundProps retAbiPlanProps
  exprLowering compileEnv abiEncoderProps vyperTypeSystem vyperValue vyperABI
  finite_map list rich_list option pair combin

Theorem qualified_log_abi_enc_plan_mods:
  !tenv ty tv sf ce tenv0.
    assignable_type tenv ty /\
    evaluate_type tenv ty = SOME tv /\
    tenv SUBMAP tenv0 /\
    abi_sfields_consistent_upto (type_value_size tv) sf tenv /\
    sfields_tenv_consistent ce.ce_struct_fields tenv0 /\
    (!t v. evaluate_type tenv0 t = SOME v ==>
      type_memory_bytes ce t = type_memory_size v) ==>
    abi_enc_plan tenv ty (type_to_abi_enc_info sf ce ty)
Proof
  rpt gen_tac >> strip_tac >>
  irule abi_encode_plan_upto >> simp[] >>
  qexists `tenv0` >> simp[]
QED
