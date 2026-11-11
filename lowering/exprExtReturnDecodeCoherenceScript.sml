(* Copied from lowering/exprSimAbiDecodeEntryCoherenceScript.sml at vyper-hol 720b09800
   (bot/opus/seq-1310-dedup), renamed, for the extcall return seam; dedup with
   that theory when both branches merge. *)
Theory exprExtReturnDecodeCoherence
Ancestors
  exprExtReturnDecodeLayout exprExtReturnDecodeMetadata
  abiCallerBuiltinInput abiCallerStructMetadata abiDecoderPrimitiveCaller abiDecoderCoherence
  vyperTyping vyperTypeSystem vyperTypeABI vyperTypeExprSoundness abiTypeBoundProps vyperValue finite_map list pair

Theorem abi_decode_descended_coherent:
  !env ty tv sf.
    abi_decode_descended_metadata ce root (type_value_size tv) env sf /\
    evaluate_type env ty = SOME tv /\ assignable_type env ty ==>
    abi_decoder_coherent ce env sf ty tv
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT bt`] >- metis_tac[abi_decoder_base_caller_coherent]
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`ArrayT t bd`] >- suspend "array"
  >~ [`StructT k`] >- suspend "struct"
  >~ [`FlagT k`] >- suspend "flag" >>
  gvs[Once assignable_type_def]
QED

Resume abi_decode_descended_coherent[array]:
  irule abi_caller_array_coherent >> simp[] >> rpt strip_tac >>
  drule evaluate_type_array_child_size >> strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  gvs[Once assignable_type_def, abi_decode_descended_metadata_def] >>
  irule abi_sfields_consistent_upto_mono >>
  qexists `type_value_size tv` >> simp[]
QED

Resume abi_decode_descended_coherent[tuple]:
  irule abi_caller_tuple_coherent >> simp[] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `MEM (EL n ts) ts` by (simp[MEM_EL] >> qexists `n` >> simp[]) >>
  drule_all evaluate_type_tuple_child_size >> strip_tac >>
  `evaluate_type env (EL n ts) = SOME (EL n tvs)` by metis_tac[] >>
  gvs[] >> qpat_x_assum `!y. type_value_size y < _ ==> _` drule >>
  disch_then irule >>
  gvs[Once assignable_type_def, EVERY_EL, abi_decode_descended_metadata_def] >>
  irule abi_sfields_consistent_upto_mono >>
  qexists `type_value_size tv` >> simp[]
QED

Resume abi_decode_descended_coherent[struct]:
  `abi_decoder_header ce env (StructT k) tv` by
    (irule abi_decode_descended_header >> simp[] >> qexists `root` >>
     gvs[abi_decode_descended_metadata_def]) >>
  `?args. FLOOKUP env k = SOME (StructArgs args)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `?fields. FLOOKUP sf (nsid_to_string k) = SOME fields /\
    MAP FST fields = MAP FST args /\
    MAP (FST o SND) fields = MAP SND args` by
    (irule abi_sfields_consistent_upto_lookup >>
     qexistsl_tac [`env`, `type_value_size tv`, `tv`] >>
     gvs[abi_decode_descended_metadata_def]) >>
  qpat_assum `evaluate_type env (StructT k) = SOME tv` mp_tac >>
  simp_tac bool_ss [Once evaluate_type_def, LET_THM] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `MAP (\(name,ty,sz). (name,ty)) fields = args` by
    (irule LIST_EQ >>
     qpat_assum `MAP FST fields = MAP FST args`
       (assume_tac o Q.AP_TERM `LENGTH`) >> gvs[LENGTH_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `MAP FST fields = MAP FST args`
       (mp_tac o Q.AP_TERM `EL x`) >>
     qpat_x_assum `MAP (FST o SND) fields = MAP SND args`
       (mp_tac o Q.AP_TERM `EL x`) >>
     simp[EL_MAP] >> Cases_on `EL x fields` >>
     Cases_on `r` >> Cases_on `EL x args` >> simp[]) >>
  simp[abi_decoder_coherent_struct_iff] >>
  qexists `tvs` >> simp[] >>
  conj_tac >- suspend "struct_sizes" >>
  suspend "struct_children"
QED

Resume abi_decode_descended_coherent[flag]:
  `abi_decoder_header ce env (FlagT k) tv` by
    (irule abi_decode_descended_header >> simp[] >> qexists `root` >>
     gvs[abi_decode_descended_metadata_def]) >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  simp[abi_decoder_coherent_flag_iff] >>
  gvs[abi_decode_descended_metadata_def, abi_decode_root_metadata_def] >>
  qpat_x_assum `!y. type_value_size y < _ ==> _` kall_tac >>
  rename1 `FLOOKUP env k = SOME (FlagArgs members)` >>
  `FLOOKUP root k = SOME (FlagArgs members)` by metis_tac[FLOOKUP_SUBMAP] >>
  metis_tac[]
QED

Resume abi_decode_descended_coherent[struct_sizes]:
  drule_all abi_decode_descended_field_sizes >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  rename1 `MEM (fname,fty,sz) fields` >>
  `?u. evaluate_type (env \\ k) fty = SOME u` by
    (drule_all abi_caller_struct_typed_field >> simp[]) >>
  `env \\ k SUBMAP env` by simp[] >>
  drule (cj 1 vyper_to_abi_type_submap) >> disch_then drule >> strip_tac >>
  `type_memory_bytes ce fty = type_memory_size u` by
    (qpat_assum `abi_decode_descended_metadata _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_descended_metadata_def] >> strip_tac >>
     drule_all abi_decode_descended_memory_size >> simp[]) >>
  metis_tac[]
QED

Resume abi_decode_descended_coherent[struct_children]:
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `MEM (EL n (MAP SND args)) (MAP SND args)` by
    (simp[MEM_EL] >> qexists `n` >> simp[]) >>
  drule_all evaluate_type_struct_child_size >> strip_tac >>
  `evaluate_type (env \\ k) (EL n (MAP SND args)) = SOME (EL n tvs)` by
    metis_tac[] >>
  gvs[] >> qpat_x_assum `!y. type_value_size y < _ ==> _` drule >>
  disch_then irule >> simp[] >> conj_tac
  >- (qpat_x_assum `assignable_type env (StructT k)` mp_tac >>
      simp[Once assignable_type_def, EVERY_MAP, EVERY_EL, EL_MAP] >>
      metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `evaluate_type env (StructT k) = SOME whole` >>
  irule abi_decode_descended_metadata_struct >> conj_tac
  >- metis_tac[] >>
  qexistsl_tac [`type_value_size whole`, `whole`] >> simp[Abbr `whole`]
QED

Finalise abi_decode_descended_coherent

Theorem abi_decode_root_coherent:
  abi_decode_root_metadata ce env /\ evaluate_type env ty = SOME tv /\
  assignable_type env ty ==>
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv
Proof
  strip_tac >> irule abi_decode_descended_coherent >> simp[] >>
  qexists `env` >> irule abi_decode_descended_metadata_init >> simp[]
QED
