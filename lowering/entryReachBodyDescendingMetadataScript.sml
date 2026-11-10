(* Semantic decoder metadata indexed by the actual descending descriptor map. *)
Theory entryReachBodyDescendingMetadata
Ancestors
  abiDecoderMembers abiDecoderTypedContract abiDecoderCoherence exprLowering

Definition entry_descending_metadata_def:
  entry_descending_metadata ce env sf ty tv di av v <=>
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    di = type_to_abi_dec_info sf ce ty /\
    has_type (vyper_to_abi_type env ty) av /\
    abi_to_vyper env ty av = SOME v /\
    type_memory_size tv = type_memory_bytes ce ty
End

Definition entry_descending_members_def:
  entry_descending_members ce env sf [] [] [] [] = T /\
  entry_descending_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) =
    (abi_decoder_coherent ce env sf ty tv /\
     entry_descending_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v /\
     entry_descending_members ce env sf tys tvs avs vs) /\
  entry_descending_members ce env sf _ _ _ _ = F
End

Theorem entry_descending_metadata_root:
  entry_descending_metadata ce env ce.ce_struct_fields ty tv di av v <=>
  abi_decoder_metadata ce env ty tv di av v
Proof
  simp[entry_descending_metadata_def, abi_decoder_metadata_def]
QED

Theorem entry_descending_metadata_transport:
  entry_descending_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v <=>
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v
Proof
  simp[entry_descending_metadata_def, abi_decoder_metadata_def]
QED

Theorem entry_descending_members_equiv:
  !tys tvs avs vs. entry_descending_members ce env sf tys tvs avs vs <=>
    abi_decoder_members ce env sf tys tvs avs vs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
  Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_descending_members_def, abi_decoder_members_def,
       entry_descending_metadata_transport]
QED

Theorem entry_descending_metadata_uint256_sf:
  entry_descending_metadata ce env sf (BaseT (UintT 256)) tv di av v <=>
  entry_descending_metadata ce env sf' (BaseT (UintT 256)) tv di av v
Proof
  simp[entry_descending_metadata_def, type_to_abi_dec_info_def]
QED
