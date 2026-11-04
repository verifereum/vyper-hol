(* Root metadata interfaces for recursively reachable decoder types. *)
Theory abiMetadataCoherence
Ancestors
  abiMetadataHeader abiMetadataLayout abiMetadataCoverage abiDecoderCoherence retAbiPlanProps
  abiReturndataSource vyperTyping vyperTypeSystem vyperValue vyperTypeABI finite_map list pair

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

Theorem abi_metadata_coherent:
  !tv ce root env sf ty.
  abi_metadata_root ce root /\ env SUBMAP root /\
  sf SUBMAP ce.ce_struct_fields /\ abi_metadata_coverage sf env ty tv /\
  assignable_type env ty ==> abi_decoder_coherent ce env sf ty tv
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_metadata_coverage_evaluate] >>
  `abi_decoder_header ce env ty tv` by
    metis_tac[abi_metadata_submap_header] >>
  Cases_on `ty`
  >- (gvs[evaluate_type_def, abi_decoder_coherent_base_iff] >>
      Cases_on `b` >> gvs[abi_decoder_scalar_valid_def, AllCaseEqs()] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[abi_decoder_scalar_valid_def, AllCaseEqs()])
  >- suspend "tuple"
  >- suspend "array"
  >- suspend "struct"
  >- suspend "flag"
  >> gvs[assignable_type_def]
QED

Resume abi_metadata_coherent[flag]:
  gvs[evaluate_type_def, AllCaseEqs(), abi_decoder_coherent_flag_iff] >>
  `FLOOKUP root p = SOME (FlagArgs m)` by metis_tac[SUBMAP_FLOOKUP_EQN] >>
  gvs[abi_metadata_root_def] >> metis_tac[]
QED

Resume abi_metadata_coherent[array]:
  gvs[evaluate_type_def, AllCaseEqs(), abi_decoder_coherent_array_iff] >>
  drule abi_metadata_coverage_array >> strip_tac >>
  gvs[assignable_type_def] >> first_x_assum irule >>
  simp[type_value_size_def] >> metis_tac[]
QED

Resume abi_metadata_coherent[tuple]:
  gvs[evaluate_type_def, AllCaseEqs(), abi_decoder_coherent_tuple_iff] >>
  drule abi_metadata_coverage_tuple >> strip_tac >>
  gvs[assignable_type_def] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `MEM (EL n tvs) tvs` by simp[EL_MEM] >>
  `MEM (EL n l) l` by simp[EL_MEM] >>
  drule_all MEM_type_value_size_TupleTV >> strip_tac >>
  first_x_assum irule >> simp[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Resume abi_metadata_coherent[struct]:
  drule abi_metadata_coverage_struct >> strip_tac >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  `env \\ p SUBMAP root` by
    (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
  `sf \\ nsid_to_string p SUBMAP ce.ce_struct_fields` by
    (irule SUBMAP_TRANS >> qexists_tac `sf` >> simp[]) >>
  `EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty) fields` by
    (irule abi_metadata_field_sizes >>
     conj_tac >- (qexistsl_tac [`nsid_to_string p`, `sf`] >> simp[]) >>
     qexistsl_tac [`env \\ p`, `root`] >> simp[] >>
     simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >> simp[] >>
     `MEM e1 (MAP SND args)` by
       (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
        simp[MEM_MAP] >> qexists_tac `(e0,e1)` >> simp[] >>
        qexists_tac `(e0,e1,e2)` >> simp[]) >>
     drule_all LIST_REL_MEM_IMP >> strip_tac >>
     drule abi_metadata_coverage_evaluate >> metis_tac[]) >>
  simp[abi_decoder_coherent_struct_iff] >>
  qexists_tac `tvs` >> simp[] >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `!y. MEM y tvs ==> type_value_size y <
      type_value_size (StructTV (ZIP(MAP FST args,tvs)))` by
    (rpt strip_tac >>
     `MEM y (MAP SND (ZIP(MAP FST args,tvs)))` by simp[MAP_ZIP] >>
     gvs[MEM_MAP, EXISTS_PROD] >>
     drule_all MEM_type_value_size_StructTV >> simp[]) >>
  qpat_x_assum `assignable_type env (StructT p)` mp_tac >>
  simp[assignable_type_def] >> strip_tac >>
  fs[LIST_REL_EL_EQN, EVERY_MAP] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  `MEM (EL n tvs) tvs` by simp[EL_MEM] >>
  `MEM (EL n (MAP SND args)) (MAP SND args)` by simp[EL_MEM] >>
  fs[EVERY_MEM] >> conj_tac >- (qexists_tac `root` >> simp[]) >>
  qpat_x_assum `MEM _ (MAP SND args)` mp_tac >>
  simp[MEM_MAP] >> strip_tac >> gvs[] >> metis_tac[]
QED

Finalise abi_metadata_coherent

Theorem abi_metadata_root_coherent:
  abi_metadata_root ce root /\ evaluate_type root ty = SOME tv /\
  assignable_type root ty ==>
  abi_decoder_coherent ce root ce.ce_struct_fields ty tv
Proof
  strip_tac >> irule abi_metadata_coherent >>
  simp[] >> conj_tac >- (qexists_tac `root` >> simp[]) >>
  irule abi_metadata_coverage_root >>
  gvs[abi_metadata_root_def]
QED

Theorem abi_metadata_return_coherent:
  abi_metadata_root ce root /\
  evaluate_type root (if needs_external_call_wrap ty then TupleT [ty] else ty) = SOME wtv /\
  assignable_type root (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  evaluate_abi_decode_return root ty data = INL v ==>
  abi_decoder_coherent ce root ce.ce_struct_fields
    (if needs_external_call_wrap ty then TupleT [ty] else ty) wtv /\
  evaluate_abi_decode_returndata root
    (if needs_external_call_wrap ty then TupleT [ty] else ty) data =
      INL (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v)
Proof
  metis_tac[abi_metadata_root_coherent, abi_return_source_observation]
QED
