(* TOP-LEVEL: classify offset navigation separately from ABI dynamic layout.
   An empty dynamic fixed array has a head slot but no payload to follow. *)
Theory abiDecoderOffset
Ancestors
  abiDecoderDynamic abiDecoderCoherence abiDecoderReadableTypes abiDecoderHeadAdequacy abiEncoder
  exprLowering compileEnv vyperABI vyperValue contractABI finite_map list rich_list pair

Theorem abi_decoder_needs_offset_iff:
  dec_info_needs_offset di <=>
    abi_decoder_dynamic di /\ di <> DecComplex T []
Proof
  Cases_on `di` >> simp[dec_info_needs_offset_def, abi_decoder_dynamic_def] >>
  rename1 `dynamic /\ _` >> Cases_on `dynamic` >> simp[]
QED

Theorem abi_decoder_static_needs_no_offset:
  ~abi_decoder_dynamic di ==> ~dec_info_needs_offset di
Proof
  simp[abi_decoder_needs_offset_iff]
QED

Theorem abi_decoder_nonempty_offset:
  di <> DecComplex T [] ==>
  dec_info_needs_offset di = abi_decoder_dynamic di
Proof
  simp[abi_decoder_needs_offset_iff]
QED

Theorem abi_decoder_base_not_empty_dynamic[local]:
  type_to_abi_dec_info sf ce (BaseT bt) <> DecComplex T []
Proof
  Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def]
QED

Theorem abi_decoder_struct_not_empty_dynamic[local]:
  type_to_abi_dec_info sf ce (StructT nsid) <> DecComplex T []
Proof
  simp[Once type_to_abi_dec_info_def] >>
  Cases_on `FLOOKUP sf (nsid_to_string nsid)` >> simp[] >>
  rename1 `SOME fields` >> Cases_on `fields` >> simp[]
QED

Theorem abi_decoder_empty_dynamic_translation:
  type_to_abi_dec_info sf ce ty = DecComplex T [] <=>
    ?elem. ty = ArrayT elem (Fixed 0) /\ is_abi_dynamic ce.ce_struct_fields elem
Proof
  Cases_on `ty` >>
  simp[abi_decoder_base_not_empty_dynamic, abi_decoder_struct_not_empty_dynamic,
    Once type_to_abi_dec_info_def] >>
  TRY (rename1 `TupleT tys` >> Cases_on `tys` >> simp[] >> NO_TAC) >>
  rename1 `ArrayT elem bound` >> Cases_on `bound` >>
  simp[Once type_to_abi_dec_info_def, GENLIST_EQ_NIL, CONJ_COMM]
QED

Theorem abi_decoder_nonempty_type_offset:
  abi_decoder_coherent ce env sf ty tv /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule abi_decoder_coherent_dynamic >> strip_tac >>
  `type_to_abi_dec_info sf ce ty <> DecComplex T []` by
    (CCONTR_TAC >> gvs[abi_decoder_empty_dynamic_translation, vyper_to_abi_type_def]) >>
  simp[abi_decoder_needs_offset_iff]
QED

Theorem abi_decoder_readable_offset:
  abi_decoder_coherent ce env sf ty tv /\ abi_decoder_readable_type env ty ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule abi_decoder_coherent_dynamic >> strip_tac >>
  simp[abi_decoder_needs_offset_iff] >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []` >> simp[] >>
  fs[abi_decoder_empty_dynamic_translation] >>
  drule abi_decoder_readable_type_head >>
  simp[vyper_to_abi_type_def]
QED

Theorem abi_decoder_positive_offset:
  abi_decoder_coherent ce env sf ty tv /\ 0 < type_slot_size tv ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule abi_decoder_coherent_dynamic >> strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  drule_all evaluated_positive_type_excludes_empty_abi_array >> strip_tac >>
  `type_to_abi_dec_info sf ce ty <> DecComplex T []` by
    (CCONTR_TAC >> gvs[abi_decoder_empty_dynamic_translation, vyper_to_abi_type_def]) >>
  simp[abi_decoder_needs_offset_iff]
QED

Theorem abi_decoder_array_child_offset:
  abi_decoder_coherent ce env sf (ArrayT ty bound) (ArrayTV tv bound) ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `0 < type_slot_size tv` by
    (qpat_x_assum `evaluate_type env (ArrayT ty bound) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()]) >>
  drule_all abi_decoder_positive_offset >> simp[]
QED
