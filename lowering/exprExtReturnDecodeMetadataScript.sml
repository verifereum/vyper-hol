(* Copied from lowering/exprSimAbiDecodeEntryMetadataScript.sml at vyper-hol 720b09800
   (bot/opus/seq-1310-dedup), renamed, for the extcall return seam; dedup with
   that theory when both branches merge. *)
(* Generic caller metadata: paired descent is bounded by evaluated type size,
   not by injectivity of source namespace names. *)
Theory exprExtReturnDecodeMetadata
Ancestors
  exprSimHypsDefs abiTypeBoundProps compileEnv vyperValue
  vyperTypeExprSoundness finite_map list pair

Definition abi_decode_root_metadata_def:
  abi_decode_root_metadata ce root <=>
    sfields_tenv_consistent ce.ce_struct_fields root /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !tv. evaluate_type root fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    (!nsid n. FLOOKUP root nsid = SOME (FlagArgs n) ==>
      ce.ce_flag_n_members (nsid_to_string nsid) = n)
End

Definition abi_decode_descended_metadata_def:
  abi_decode_descended_metadata ce root n env sf <=>
    abi_decode_root_metadata ce root /\ env SUBMAP root /\
    sf SUBMAP ce.ce_struct_fields /\ abi_sfields_consistent_upto n sf env
End

Theorem abi_decode_root_metadata_inv:
  expr_sim_inv ce cx env es ==>
  abi_decode_root_metadata ce (get_tenv cx)
Proof
  simp[expr_sim_inv_def, abi_decode_root_metadata_def] >> metis_tac[]
QED

Theorem abi_decode_descended_metadata_init:
  abi_decode_root_metadata ce root ==>
  abi_decode_descended_metadata ce root n root ce.ce_struct_fields
Proof
  simp[abi_decode_descended_metadata_def, abi_decode_root_metadata_def] >>
  metis_tac[abi_sfields_consistent_upto_init]
QED

Theorem abi_decode_descended_metadata_struct:
  abi_decode_descended_metadata ce root n env sf /\
  FLOOKUP env k = SOME (StructArgs args) /\
  evaluate_type env (StructT k) = SOME v /\ type_value_size v <= n /\
  m < type_value_size v ==>
  abi_decode_descended_metadata ce root m
    (env \\ k) (sf \\ nsid_to_string k)
Proof
  rw[abi_decode_descended_metadata_def]
  >- (irule SUBMAP_TRANS >> qexists `env` >> simp[])
  >- (irule SUBMAP_TRANS >> qexists `sf` >> simp[]) >>
  irule abi_sfields_consistent_upto_domsub >> metis_tac[]
QED

Theorem abi_decode_descended_field_sizes:
  abi_decode_descended_metadata ce root n env sf /\
  FLOOKUP sf name = SOME fields ==>
  EVERY (\(fname,fty,sz). !tv. evaluate_type env fty = SOME tv ==>
    sz = type_memory_size tv) fields
Proof
  rw[abi_decode_descended_metadata_def, abi_decode_root_metadata_def] >>
  `FLOOKUP ce.ce_struct_fields name = SOME fields` by
    metis_tac[FLOOKUP_SUBMAP] >>
  first_x_assum drule >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  drule (cj 1 vyper_to_abi_type_submap) >>
  metis_tac[]
QED
