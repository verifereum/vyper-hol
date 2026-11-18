(* Constructor observations for exact heterogeneous calldata members. *)
Theory calldataExactMemberValues
Ancestors
  vyperCalldata abiDecoderCoherence calldataReconstruction
  entryReachBodyMemberPrefix abiStaticDynarrayLayout vyperTypeABI
  vyperTypeDefaults valueEncodingTyping bodyPtrDefs
  valueEncodingDefs valueEncoding vyperTyping list arithmetic

Theorem calldata_exact_tuple_windows[local]:
  LIST_REL value_has_type tvs vs /\
  (!i mem'. i < LENGTH tvs /\ mem_agree_outside dirty mem mem' ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem') ==>
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) d mem /\
  (!mem'. mem_agree_outside dirty mem mem' ==>
    tuple_in_memory vs tvs d mem')
Proof
  strip_tac >>
  `LENGTH vs = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `!mem'. mem_agree_outside dirty mem mem' ==>
    tuple_in_memory vs tvs d mem'` by
    (rpt strip_tac >> simp[entry_member_memory_indexed] >> metis_tac[]) >>
  `tuple_in_memory vs tvs d mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all calldata_tuple_values_typed_memory >> simp[]
QED

Theorem calldata_exact_tuple_member_observations:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  cd_decode_list F cd tvs p 0 = decoded /\
  (!vs. decoded = SOME vs ==>
    LIST_REL value_has_type tvs vs /\
    (!i mem'. i < LENGTH tvs /\ mem_agree_outside dirty mem mem' ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem')) ==>
  case decoded of
    NONE => cd_decode F cd (TupleTV tvs) p = NONE
  | SOME vs =>
      cd_decode F cd (TupleTV tvs) p = SOME (ArrayV (TupleV vs)) /\
      value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
      val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) d mem /\
      (!mem'. mem_agree_outside dirty mem mem' ==>
        val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) d mem')
Proof
  strip_tac >> Cases_on `decoded` >> gvs[Once cd_decode_def] >>
  drule_all calldata_exact_tuple_windows >> strip_tac >>
  simp[val_in_memory_def]
QED

Theorem calldata_exact_struct_member_observations:
  abi_decoder_coherent ce env sf (StructT nsid)
    (StructTV (ZIP (MAP FST args,tvs))) /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid)
    (sf \\ nsid_to_string nsid)) (MAP SND args) tvs /\
  cd_decode_list F cd tvs p 0 = decoded /\
  (!vs. decoded = SOME vs ==>
    LIST_REL value_has_type tvs vs /\
    (!i mem'. i < LENGTH tvs /\ mem_agree_outside dirty mem mem' ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem')) ==>
  case decoded of
    NONE => cd_decode F cd (StructTV (ZIP (MAP FST args,tvs))) p = NONE
  | SOME vs =>
      cd_decode F cd (StructTV (ZIP (MAP FST args,tvs))) p =
        SOME (StructV (ZIP (MAP FST args,vs))) /\
      value_has_type (StructTV (ZIP (MAP FST args,tvs)))
        (StructV (ZIP (MAP FST args,vs))) /\
      val_wf (StructTV (ZIP (MAP FST args,tvs)))
        (StructV (ZIP (MAP FST args,vs))) /\
      val_in_memory (StructTV (ZIP (MAP FST args,tvs)))
        (StructV (ZIP (MAP FST args,vs))) d mem /\
      (!mem'. mem_agree_outside dirty mem mem' ==>
        val_in_memory (StructTV (ZIP (MAP FST args,tvs)))
          (StructV (ZIP (MAP FST args,vs))) d mem')
Proof
  strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  Cases_on `decoded` >> gvs[Once cd_decode_def, MAP_ZIP] >>
  rename1 `LIST_REL value_has_type tvs vs` >>
  `LENGTH vs = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  drule_all calldata_exact_tuple_windows >> strip_tac >>
  `struct_has_type (ZIP (MAP FST args,tvs)) (ZIP (MAP FST args,vs))` by
    (irule vyperTypeABITheory.struct_has_type_ZIP >>
     simp[values_have_types_LIST_REL]) >>
  `value_has_type (StructTV (ZIP (MAP FST args,tvs)))
     (StructV (ZIP (MAP FST args,vs)))` by simp[value_has_type_def] >>
  simp[] >> conj_tac
  >- metis_tac[value_has_type_val_wf] >>
  simp[val_in_memory_def] >> conj_tac
  >- (irule static_fields_memory_zip >> simp[MAP_ZIP] >>
      gvs[val_in_memory_def]) >>
  rpt strip_tac >> irule static_fields_memory_zip >> simp[MAP_ZIP]
QED
