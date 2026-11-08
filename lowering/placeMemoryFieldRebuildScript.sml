Theory placeMemoryFieldRebuild
Ancestors
  placeMemoryIndexRebuild placeMemoryTypedBase loweringPosts valueEncoding valueEncodingDefs
  vyperTyping alist list rich_list arithmetic valueEncodingTyping

(* Resolve the first named field once, simultaneously in its layout and update. *)
Theorem mem_field_offset_update_zip:
  !names tvs vs id k ftv z.
  LENGTH names = LENGTH tvs /\ LENGTH names = LENGTH vs /\
  mem_field_offset (ZIP (names,tvs)) id = SOME (k,ftv) ==>
  ?i. i < LENGTH names /\
      k = type_memory_size_list (TAKE i tvs) /\ ftv = EL i tvs /\
      AFUPDKEY id (K z) (ZIP (names,vs)) = ZIP (names,LUPDATE z i vs)
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[mem_field_offset_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[mem_field_offset_def, AllCaseEqs()] >> strip_tac
  >- (qexists_tac `0` >>
      simp[AFUPDKEY_def, type_memory_size_def, LUPDATE_def]) >>
  PairCases_on `z'` >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >> simp[] >>
  disch_then drule >> disch_then (qspec_then `z` strip_assume_tac) >>
  qexists_tac `SUC i` >>
  simp[AFUPDKEY_def, LUPDATE_def] >>
  simp_tac std_ss [TAKE_def, EL, TL, HD, type_memory_size_def] >>
  simp[]
QED

Theorem struct_update_bounded_frame:
  value_has_type (StructTV ftypes) (StructV fields) /\
  mem_field_offset ftypes id = SOME (k,ftv) /\
  val_in_memory (StructTV ftypes) (StructV fields) off mem /\
  val_in_memory ftv z (off + k) mem' /\
  (!a n. off <= a /\ a + n <= off + type_memory_size_fields ftypes /\
    (a + n <= off + k \/ off + k + type_memory_size ftv <= a) ==>
    mem_bytes_at a n mem' = mem_bytes_at a n mem) ==>
  val_in_memory (StructTV ftypes) (StructV (AFUPDKEY id (K z) fields)) off mem'
Proof
  strip_tac >>
  `?names tvs. ftypes = ZIP (names,tvs) /\ LENGTH names = LENGTH tvs` by
    (qexistsl_tac [`MAP FST ftypes`, `MAP SND ftypes`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Induct_on `ftypes` >> simp[] >> gen_tac >> PairCases_on `h` >> simp[]) >> gvs[] >>
  `struct_has_type (ZIP (names,tvs)) fields /\
   fields_val_wf fields (ZIP (names,tvs))` by
    (gvs[value_has_type_def] >>
     metis_tac[cj 5 value_has_type_val_wf]) >>
  drule_all typed_memory_struct_values >> strip_tac >> gvs[] >>
  qspecl_then [`names`, `tvs`, `vs`] mp_tac mem_field_offset_update_zip >> simp[] >>
  disch_then drule >> disch_then (qspec_then `z` strip_assume_tac) >>
  gvs[] >>
  gvs[Once val_in_memory_def, typed_memory_fields_tuple_zip, LENGTH_LUPDATE,
      type_memory_size_fields_zip] >>
  simp[Once val_in_memory_def, typed_memory_fields_tuple_zip, LENGTH_LUPDATE] >>
  irule tuple_update_bounded_frame >> simp[] >>
  qexists_tac `mem` >> simp[] >> first_assum ACCEPT_TAC
QED
