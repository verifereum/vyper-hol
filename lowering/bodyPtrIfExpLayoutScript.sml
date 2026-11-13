Theory bodyPtrIfExpLayout
Ancestors bodyPtrIfExpWideningAudit memoryLocalRhsProps compileEnv context supportedTypes vyperTypeSystem

Theorem ifexp_supported_word_fits_eq:
  !st dt. supported_word_type st /\ arg_type_fits st dt ==> st = dt
Proof
  Cases_on `st` >> Cases_on `dt` >>
  simp[supported_word_type_def, arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT bt) (BaseT bu)` >>
  Cases_on `bu` >> Cases_on `bt` >>
  simp[supported_word_type_def, arg_type_fits_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, arg_type_fits_def] >>
  Cases_on `b` >> simp[arg_type_fits_def]
QED

Theorem ifexp_supported_scalar_fits_size:
  !ce st dt.
    supported_scalar_type st /\ arg_type_fits st dt ==>
    type_memory_bytes ce st <= type_memory_bytes ce dt
Proof
  rpt strip_tac >>
  gvs[supported_scalar_type_def]
  >- (drule_all ifexp_supported_word_fits_eq >> simp[]) >>
  irule arg_type_fits_bytestring_memory_bytes >> simp[] >>
  Cases_on `st` >> gvs[supported_string_type_def] >>
  Cases_on `b` >> gvs[supported_string_type_def, is_bytestring_type_def] >>
  Cases_on `b'` >> gvs[supported_string_type_def, is_bytestring_type_def]
QED

Theorem ifexp_ordered_sums:
  !xs ys. LIST_REL (\x y:num. x <= y) xs ys ==> SUM xs <= SUM ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem ifexp_ordered_sums_equal:
  !xs ys. LIST_REL (\x y:num. x <= y) xs ys /\ SUM xs = SUM ys ==> xs = ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `SUM xs <= SUM t` by metis_tac[ifexp_ordered_sums] >>
  `h = h' /\ SUM xs = SUM t` by decide_tac >>
  gvs[] >> first_x_assum irule >> simp[]
QED

Theorem ifexp_supported_scalar_fits_punnable:
  !ce st dt. supported_scalar_type st /\ arg_type_fits st dt ==> punnable ce st dt
Proof
  Cases_on `st` >> Cases_on `dt` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def, punnable_def, arg_type_fits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def, arg_type_fits_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, supported_string_type_def, arg_type_fits_def]
QED

Theorem ifexp_scalar_list_sizes_ordered:
  !ce ts us. EVERY supported_scalar_type ts /\ arg_types_fit ts us ==>
    LIST_REL (\x y:num. x <= y)
      (MAP (type_memory_bytes ce) ts) (MAP (type_memory_bytes ce) us)
Proof
  gen_tac >> Induct >> Cases_on `us` >>
  simp[arg_type_fits_def] >> rpt strip_tac
  >- metis_tac[ifexp_supported_scalar_fits_size] >>
  first_x_assum irule >> simp[]
QED

Theorem ifexp_scalar_list_equal_punnable:
  !ce ts us. EVERY supported_scalar_type ts /\ arg_types_fit ts us /\
    MAP (type_memory_bytes ce) ts = MAP (type_memory_bytes ce) us ==>
    punnable_list ce ts us
Proof
  gen_tac >> Induct >> Cases_on `us` >>
  simp[arg_type_fits_def, punnable_def] >> rpt strip_tac
  >- metis_tac[ifexp_supported_scalar_fits_punnable] >>
  first_x_assum irule >> simp[]
QED

Theorem ifexp_scalar_tuple_reverse_size_layout:
  !ce ts us. EVERY supported_scalar_type ts /\ arg_types_fit ts us /\
    type_memory_bytes ce (TupleT us) <= type_memory_bytes ce (TupleT ts) ==>
    same_memory_layout ce (TupleT ts) (TupleT us)
Proof
  rpt strip_tac >> drule_all ifexp_scalar_list_sizes_ordered >>
  disch_then (qspec_then `ce` assume_tac) >>
  drule ifexp_ordered_sums >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) ts) = SUM (MAP (type_memory_bytes ce) us)` by
    (gvs[type_memory_bytes_def, SF ETA_ss] >> decide_tac) >>
  drule_all ifexp_ordered_sums_equal >> strip_tac >>
  simp[same_memory_layout_def, punnable_def, type_memory_bytes_def, SF ETA_ss] >>
  irule ifexp_scalar_list_equal_punnable >> simp[]
QED

Theorem ifexp_supported_word_memory_bytes:
  !ce ty. supported_word_type ty ==> type_memory_bytes ce ty = 32
Proof
  Cases_on `ty` >> simp[supported_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, type_memory_bytes_def]
QED

Theorem ifexp_supported_fits_size:
  !ce st dt. supported_value_type [] st /\ arg_type_fits st dt ==>
    type_memory_bytes ce st <= type_memory_bytes ce dt
Proof
  rpt strip_tac >>
  Cases_on `supported_scalar_type st`
  >- metis_tac[ifexp_supported_scalar_fits_size] >>
  Cases_on `st` >> Cases_on `dt` >>
  gvs[supported_value_type_def, supported_struct_fields_def, arg_type_fits_def]
  >~ [`EVERY supported_scalar_type _`] >- (
    drule_all ifexp_scalar_list_sizes_ordered >>
    disch_then (qspec_then `ce` mp_tac) >>
    simp[type_memory_bytes_def, SF ETA_ss] >>
    metis_tac[SRULE [SF ETA_ss] ifexp_ordered_sums]) >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
  rename1 `arg_type_fits et eu` >>
  `et = eu` by metis_tac[ifexp_supported_word_fits_eq] >>
  `type_memory_bytes ce et = 32` by metis_tac[ifexp_supported_word_memory_bytes] >>
  gvs[type_memory_bytes_def]
QED

Theorem ifexp_supported_reverse_size_layout:
  !ce st dt. supported_value_type [] st /\ arg_type_fits st dt /\
    type_memory_bytes ce dt <= type_memory_bytes ce st ==>
    same_memory_layout ce st dt
Proof
  rpt strip_tac >>
  `type_memory_bytes ce st = type_memory_bytes ce dt` by
    (drule_all ifexp_supported_fits_size >>
     disch_then (qspec_then `ce` mp_tac) >> decide_tac) >>
  Cases_on `supported_scalar_type st`
  >- (simp[same_memory_layout_def] >>
      metis_tac[ifexp_supported_scalar_fits_punnable]) >>
  Cases_on `st` >> Cases_on `dt` >>
  gvs[supported_value_type_def, supported_struct_fields_def, arg_type_fits_def]
  >~ [`EVERY supported_scalar_type _`] >-
    (irule ifexp_scalar_tuple_reverse_size_layout >> simp[]) >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
  rename1 `arg_type_fits et eu` >>
  `et = eu` by metis_tac[ifexp_supported_word_fits_eq] >>
  gvs[same_memory_layout_def, punnable_def] >>
  irule ifexp_supported_scalar_fits_punnable >>
  simp[supported_scalar_type_def]
QED
