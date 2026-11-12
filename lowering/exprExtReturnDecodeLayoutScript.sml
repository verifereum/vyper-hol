(* Copied from lowering/exprSimAbiDecodeEntryLayoutScript.sml at vyper-hol 720b09800
   (bot/opus/seq-1310-dedup), renamed, for the extcall return seam; dedup with
   that theory when both branches merge. *)
(* Generic layout and ABI headers from caller metadata, with no namespace
   construction witness. *)
Theory exprExtReturnDecodeLayout
Ancestors
  exprExtReturnDecodeMetadata abiCallerAbiShape abiCallerTupleLayout
  typedMemoryCopy abiTypeBoundProps vyperTypeExprSoundness
  compileEnv vyperValue finite_map list pair combin

Theorem abi_decode_fields_pair_map[local]:
  !fields args.
    MAP FST fields = MAP FST args /\
    MAP (FST o SND) fields = MAP SND args ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args
Proof
  Induct_on `fields` >> rpt gen_tac >> Cases_on `args` >> simp[] >>
  PairCases_on `h` >> PairCases_on `h'` >> simp[]
QED

Theorem abi_decode_abi_shape_upto:
  !env ty tv sf.
    evaluate_type env ty = SOME tv /\
    abi_sfields_consistent_upto (type_value_size tv) sf env ==>
    abi_caller_abi_shape sf env ty
Proof
  measureInduct_on `type_value_size tv` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT bt`] >- simp[abi_caller_abi_shape_base]
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`ArrayT t bd`] >- suspend "array"
  >~ [`StructT k`] >- suspend "struct" >>
  simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def]
QED

Resume abi_decode_abi_shape_upto[tuple]:
  irule abi_caller_abi_shape_tuple >> simp[EVERY_MEM] >>
  rpt strip_tac >>
  drule_all evaluate_type_tuple_child_size >> strip_tac >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  irule abi_sfields_consistent_upto_mono >>
  qexists `type_value_size tv` >> simp[]
QED

Resume abi_decode_abi_shape_upto[array]:
  irule abi_caller_abi_shape_array >>
  drule evaluate_type_array_child_size >> strip_tac >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  irule abi_sfields_consistent_upto_mono >>
  qexists `type_value_size tv` >> simp[]
QED

Resume abi_decode_abi_shape_upto[struct]:
  `?args. FLOOKUP env k = SOME (StructArgs args)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `type_value_size tv <= type_value_size tv` by simp[] >>
  drule_all abi_sfields_consistent_upto_lookup >> strip_tac >>
  irule abi_caller_abi_shape_struct >>
  qexistsl_tac [`args`, `fields`] >> simp[] >>
  conj_tac >- metis_tac[abi_decode_fields_pair_map] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all evaluate_type_struct_child_size >> strip_tac >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  irule abi_sfields_consistent_upto_domsub >> metis_tac[]
QED

Finalise abi_decode_abi_shape_upto

Theorem abi_decode_descended_memory_size:
  abi_decode_root_metadata ce root /\ env SUBMAP root /\
  evaluate_type env ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv
Proof
  strip_tac >> drule (cj 1 vyper_to_abi_type_submap) >>
  disch_then drule >> strip_tac >>
  irule typed_copy_memory_size >> qexists `root` >>
  gvs[abi_decode_root_metadata_def] >> metis_tac[]
QED

Theorem abi_decode_descended_header:
  abi_decode_root_metadata ce root /\ env SUBMAP root /\
  evaluate_type env ty = SOME tv ==>
  abi_decoder_header ce env ty tv
Proof
  strip_tac >> irule abi_caller_header_from_shape >> simp[] >>
  conj_tac
  >- (drule_all abi_decode_descended_memory_size >> simp[]) >>
  drule (cj 1 vyper_to_abi_type_submap) >> disch_then drule >> strip_tac >>
  `abi_caller_abi_shape ce.ce_struct_fields root ty` suffices_by
    simp[abi_caller_abi_shape_def] >>
  irule abi_decode_abi_shape_upto >> qexists `tv` >> simp[] >>
  irule abi_sfields_consistent_upto_init >>
  gvs[abi_decode_root_metadata_def]
QED
