(* Root metadata interfaces for recursively reachable decoder types. *)
Theory abiMetadataCoherence
Ancestors
  abiMetadataHeader abiMetadataLayout abiMetadataCoverage abiDecoderCoherence retAbiPlanProps
  finite_map list pair

Definition abi_metadata_root_def:
  abi_metadata_root ce root <=>
    sfields_tenv_consistent ce.ce_struct_fields root /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !v. evaluate_type root fty = SOME v ==>
                              sz = type_memory_size v) fields) /\
    (!nsid n. FLOOKUP root nsid = SOME (FlagArgs n) ==>
      ce.ce_flag_n_members (nsid_to_string nsid) = n)
End

Theorem abi_metadata_submap_header:
  abi_metadata_root ce root /\ env SUBMAP root /\
  evaluate_type env ty = SOME tv ==> abi_decoder_header ce env ty tv
Proof
  strip_tac >> drule_all (cj 1 vyper_to_abi_type_submap) >> strip_tac >>
  `abi_decoder_header ce root ty tv` by
    (irule metadata_decoder_header >> gvs[abi_metadata_root_def] >> metis_tac[]) >>
  gvs[abi_decoder_header_def]
QED

Theorem abi_metadata_field_sizes:
  abi_metadata_root ce root /\ sf SUBMAP ce.ce_struct_fields /\
  FLOOKUP sf name = SOME fields /\ env SUBMAP root /\
  EVERY (\(fname,fty,sz). ?v. evaluate_type env fty = SOME v) fields ==>
  EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty) fields
Proof
  strip_tac >>
  `FLOOKUP ce.ce_struct_fields name = SOME fields` by
    metis_tac[SUBMAP_FLOOKUP_EQN] >>
  gvs[abi_metadata_root_def, EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> gvs[] >>
  qpat_x_assum `!e. MEM e fields ==> _`
    (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_type_submap) >> strip_tac >>
  `e2 = type_memory_size v` by
    (qpat_assum `!name fields. _` (qspecl_then [`name`, `fields`] mp_tac) >>
     simp[] >> disch_then (qspec_then `(e0,e1,e2)` mp_tac) >> simp[]) >>
  `type_memory_size v = type_memory_bytes ce e1` suffices_by simp[] >>
  sym_tac >> irule metadata_type_memory_size >>
  qexists_tac `root` >> simp[EVERY_MEM] >> metis_tac[]
QED
