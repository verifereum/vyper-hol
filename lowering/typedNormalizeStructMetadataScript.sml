(* Ordered nominal metadata for recursive normalization consumers. *)
Theory typedNormalizeStructMetadata
Ancestors
  typedMemoryCopy typedCopyMetadata typedCopyDomain valueEncodingTyping
  vyperTypeExprSoundness vyperTypeABI list rich_list alist finite_map
  compileEnv loweringStateRelDefs vyperTypeSystem vyperValue vyperTyping vyperTypeDefaults valueEncoding valueEncodingDefs

Theorem normalize_struct_metadata:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty (StructT name) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv (StructT name) = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v ==>
  sty = StructT name /\ stv = dtv /\
  ?fields names tvs vs.
    FLOOKUP ce.ce_struct_fields (nsid_to_string name) = SOME fields /\
    names = MAP FST fields /\ ALL_DISTINCT names /\
    LENGTH names = LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
    dtv = StructTV (ZIP (names,tvs)) /\ v = StructV (ZIP (names,vs)) /\
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv)
      (MAP (FST o SND) fields) tvs /\
    EVERY2 val_wf tvs vs /\ values_have_types tvs vs /\
    (!fname fty sz. MEM (fname,fty,sz) fields ==>
      ALOOKUP fields fname = SOME (fty,sz) /\ sz = type_memory_bytes ce fty /\
      type_rank ce.ce_struct_fields fty < type_rank ce.ce_struct_fields (StructT name))
Proof
  strip_tac >>
  `sty = StructT name` by metis_tac[typed_copy_struct_widening] >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP ce.ce_struct_fields (nsid_to_string name) = SOME fields /\
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >> drule OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
    values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    metis_tac[typed_copy_struct_values, LENGTH_MAP] >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  qexistsl_tac [`tvs`, `vs`] >>
  `ALL_DISTINCT (MAP FST fields)` by metis_tac[] >>
  `LENGTH fields = LENGTH tvs` by metis_tac[LENGTH_MAP] >>
  `ALL_DISTINCT (MAP FST args)` by metis_tac[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs` by metis_tac[] >>
  simp[] >> conj_tac >- suspend "sizes" >>
  conj_tac >- suspend "wf" >> suspend "members"
QED
Resume normalize_struct_metadata[sizes]:
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs` by
    (irule OPT_MMAP_LIST_REL >> simp[]) >>
  irule LIST_REL_mono >> first_assum (irule_at Any) >>
  rpt strip_tac >> fs[] >> irule typed_copy_memory_size >>
  qexists_tac `tenv` >> simp[] >> metis_tac[]
QED
Resume normalize_struct_metadata[wf]:
  gvs[values_have_types_LIST_REL] >>
  irule LIST_REL_mono >> first_assum (irule_at Any) >>
  simp[value_has_type_val_wf]
QED
Resume normalize_struct_metadata[members]:
  `EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty) fields` by
    (irule typed_copy_struct_field_bytes >> qexistsl_tac [`tenv`, `tvs`] >>
     simp[] >> reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >> irule typed_copy_memory_size >> qexists_tac `tenv` >>
     simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
  conj_tac
  >- (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `MEM (fname,fty,sz) (get_struct_fields ce.ce_struct_fields (nsid_to_string name))` by
    simp[get_struct_fields_def] >>
  drule_all member_rank_lt_struct >> simp[type_rank_def, nsid_to_string_def]
QED
Finalise normalize_struct_metadata
