(* Descriptor invariant required by the encoder's static-array helper.
   Actual type translation supplies it independently of runtime memory. *)
Theory abiEncoderAdmissible
Ancestors
  abiEncoder exprLowering compileEnv emitHelper list rich_list pair

Definition abi_encoder_static_leaf_def:
  abi_encoder_static_leaf ei <=>
    ei = AbiPrimWord \/ (?sz. ei = AbiCopy sz) \/ ei = AbiComplex []
End

Definition abi_encoder_admissible_def:
  abi_encoder_admissible AbiPrimWord = T /\
  abi_encoder_admissible (AbiCopy sz) = T /\
  abi_encoder_admissible (AbiBytestring n) = T /\
  abi_encoder_admissible (AbiDynArray ei abi_sz mem_sz dyn) =
    (abi_encoder_admissible ei /\ (dyn \/ abi_encoder_static_leaf ei)) /\
  abi_encoder_admissible (AbiComplex infos) = abi_encoder_members_admissible infos /\
  abi_encoder_members_admissible [] = T /\
  abi_encoder_members_admissible ((ei,abi_sz,mem_sz,dyn)::infos) =
    (abi_encoder_admissible ei /\ abi_encoder_members_admissible infos)
End

Theorem abi_encoder_members_admissible_every:
  !infos. abi_encoder_members_admissible infos <=>
    EVERY (\(ei,abi_sz,mem_sz,dyn). abi_encoder_admissible ei) infos
Proof
  Induct_on `infos` >- simp[abi_encoder_admissible_def] >>
  qx_gen_tac `info` >> PairCases_on `info` >>
  simp[abi_encoder_admissible_def]
QED

Theorem abi_encoder_static_leaf_admissible:
  abi_encoder_static_leaf ei ==> abi_encoder_admissible ei
Proof
  rw[abi_encoder_static_leaf_def] >> simp[abi_encoder_admissible_def]
QED

Theorem abi_encode_static_info_agrees:
  abi_encoder_static_leaf ei ==>
  compile_abi_encode_static_info dst src ei = compile_abi_encode_to_buf dst src ei
Proof
  rw[abi_encoder_static_leaf_def] >>
  simp[compile_abi_encode_static_info_def, Once compile_abi_encode_child_def]
QED

Theorem abi_encoder_translation_static_leaf:
  !sf ce ty. ~is_abi_dynamic ce.ce_struct_fields ty ==>
    abi_encoder_static_leaf (type_to_abi_enc_info sf ce ty)
Proof
  Cases_on `ty` >> simp[type_to_abi_enc_info_def, abi_encoder_static_leaf_def, is_abi_dynamic_def] >>
  FIRST [rename1 `BaseT bt` >> Cases_on `bt`, ALL_TAC] >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, ALL_TAC] >>
  FIRST [rename1 `ArrayT elem bound` >> Cases_on `bound`, ALL_TAC] >>
  simp[type_to_abi_enc_info_def, abi_encoder_static_leaf_def, is_abi_dynamic_def]
QED

Theorem abi_encoder_translation_static_alternative:
  is_abi_dynamic ce.ce_struct_fields ty \/ abi_encoder_static_leaf (type_to_abi_enc_info sf ce ty)
Proof
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >> simp[abi_encoder_translation_static_leaf]
QED

Theorem abi_encoder_translation_fixed_admissible:
  (!i. is_abi_dynamic ce.ce_struct_fields (ArrayT ty (Fixed n)) /\ i < n ==>
    abi_encoder_admissible (type_to_abi_enc_info sf ce ty)) ==>
  abi_encoder_admissible (type_to_abi_enc_info sf ce (ArrayT ty (Fixed n)))
Proof
  strip_tac >> Cases_on `is_abi_dynamic ce.ce_struct_fields (ArrayT ty (Fixed n))` >>
  asm_simp_tac bool_ss [Once type_to_abi_enc_info_def, abi_encoder_admissible_def,
    abi_encoder_members_admissible_every] >>
  simp_tac bool_ss [EVERY_GENLIST] >> qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_translation_tuple_admissible:
  (!ty. is_abi_dynamic ce.ce_struct_fields (TupleT tys) /\ MEM ty tys ==>
    abi_encoder_admissible (type_to_abi_enc_info sf ce ty)) ==>
  abi_encoder_admissible (type_to_abi_enc_info sf ce (TupleT tys))
Proof
  strip_tac >> Cases_on `is_abi_dynamic ce.ce_struct_fields (TupleT tys)` >>
  asm_simp_tac bool_ss [Once type_to_abi_enc_info_def, abi_encoder_admissible_def,
    abi_encoder_members_admissible_every] >>
  simp_tac bool_ss [EVERY_MAP, EVERY_MEM] >> qx_gen_tac `ty` >> strip_tac >>
  first_x_assum (qspec_then `ty` mp_tac) >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_translation_struct_admissible:
  (!name fields fn ty sz. is_abi_dynamic ce.ce_struct_fields (StructT nsid) /\
    name = nsid_to_string nsid /\ FLOOKUP sf name = SOME fields /\ MEM (fn,ty,sz) fields ==>
    abi_encoder_admissible (type_to_abi_enc_info (sf \\ name) ce ty)) ==>
  abi_encoder_admissible (type_to_abi_enc_info sf ce (StructT nsid))
Proof
  strip_tac >> Cases_on `is_abi_dynamic ce.ce_struct_fields (StructT nsid)` >>
  asm_simp_tac bool_ss [Once type_to_abi_enc_info_def, abi_encoder_admissible_def, LET_THM] >>
  Cases_on `FLOOKUP sf (nsid_to_string nsid)` >>
  gvs[abi_encoder_admissible_def, abi_encoder_members_admissible_every,
    EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem abi_encoder_translation_admissible:
  !sf ce ty. abi_encoder_admissible (type_to_abi_enc_info sf ce ty)
Proof
  ho_match_mp_tac type_to_abi_enc_info_ind >> rpt conj_tac >> rpt strip_tac >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def,
    abi_encoder_admissible_def, abi_encoder_members_admissible_every] >>
  FIRST [irule abi_encoder_translation_static_alternative,
    irule (SIMP_RULE bool_ss [Once type_to_abi_enc_info_def] abi_encoder_translation_fixed_admissible) >>
      fs[],
    irule (SIMP_RULE bool_ss [Once type_to_abi_enc_info_def] abi_encoder_translation_tuple_admissible) >>
      fs[],
    irule (SIMP_RULE bool_ss [Once type_to_abi_enc_info_def] abi_encoder_translation_struct_admissible) >>
      fs[]]
QED
