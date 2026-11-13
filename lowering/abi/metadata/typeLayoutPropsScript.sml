(* TOP-LEVEL: checked compiler environments allocate the complete evaluated
   source footprint for every type. Helpers compose arrays and tuples and
   recover struct sizes from the actual, fully resolved metadata producer. *)
Theory typeLayoutProps
Ancestors
  structSourceProps structLayoutProps typedCopyMetadata typedCopyProducer
  compileVyper compileEnv valueEncoding valueLoadProps memoryValueAbiTuple
  vyperContext vyperValue vyperAST vyperTypeABI vyperTypeValues vyperTypeExprSoundness
  vyperTypeContract vfmConstants finite_map list pair combin arithmetic
Libs
  legacyInduction

Theorem type_memory_size_list_sum:
  !tvs. type_memory_size_list tvs = SUM (MAP type_memory_size tvs)
Proof
  Induct >> simp[type_memory_size_def]
QED

Theorem type_memory_bytes_base_evaluated:
  !cenv tenv bt tv.
    evaluate_type tenv (BaseT bt) = SOME tv ==>
    type_memory_bytes cenv (BaseT bt) = type_memory_size tv
Proof
  rpt strip_tac >> drule evaluate_type_base_identity >> DISCH_TAC >> gvs[] >>
  Cases_on `bt` >> simp[type_memory_bytes_def, type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[type_memory_bytes_def, type_memory_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem type_memory_bytes_struct_evaluated:
  !tops cenv nsid tv.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) (StructT nsid) = SOME tv ==>
    type_memory_bytes cenv (StructT nsid) = type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `evaluate_types _ (MAP SND source_args) [] = SOME field_tvs` >>
  drule (CONJUNCT2 evaluate_type_mono) >> DISCH_TAC >>
  drule_all evaluate_types_LIST_REL >> DISCH_TAC >>
  drule_all evaluated_struct_metadata_types >> strip_tac >>
  rename1 `FLOOKUP (make_struct_fields_map tops) (nsid_to_string nsid) = SOME fields` >>
  `MAP (SND o SND) fields = MAP type_memory_size field_tvs` by
    (mp_tac (Q.SPECL [`tops`, `nsid_to_string nsid`, `fields`, `field_tvs`]
      make_struct_fields_map_sizes) >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  `LENGTH source_args = LENGTH field_tvs` by (drule LIST_REL_LENGTH >> simp[]) >>
  simp[type_memory_bytes_def, type_memory_size_def, type_memory_size_fields_list,
    type_memory_size_list_sum, MAP_ZIP, get_struct_fields_def]
QED

Definition type_memory_layout_def:
  type_memory_layout ty <=>
    !tops cenv tv.
      struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
      evaluate_type (type_env tops) ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv
End

Theorem type_memory_layout_base:
  !bt. type_memory_layout (BaseT bt)
Proof
  simp[type_memory_layout_def] >> rpt strip_tac >>
  drule_all type_memory_bytes_base_evaluated >> simp[]
QED

Theorem type_memory_layout_struct:
  !nsid. type_memory_layout (StructT nsid)
Proof
  simp[type_memory_layout_def] >> rpt strip_tac >>
  drule_all type_memory_bytes_struct_evaluated >> simp[]
QED

Theorem type_memory_layout_flag:
  !nsid. type_memory_layout (FlagT nsid)
Proof
  simp[type_memory_layout_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def, type_memory_size_def]
QED

Theorem type_memory_layout_none:
  type_memory_layout NoneT
Proof
  simp[type_memory_layout_def, evaluate_type_def, type_memory_bytes_def, type_memory_size_def]
QED

Theorem type_memory_layout_array:
  !elem_ty array_bound.
    type_memory_layout elem_ty ==> type_memory_layout (ArrayT elem_ty array_bound)
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [type_memory_layout_def] >>
  rpt strip_tac >> drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (type_env tops) elem_ty = SOME elem_tv` >>
  qpat_x_assum `type_memory_layout elem_ty` (mp_tac o REWRITE_RULE [type_memory_layout_def]) >>
  disch_then (qspecl_then [`tops`, `cenv`, `elem_tv`] mp_tac) >>
  impl_tac >- simp[] >> DISCH_TAC >> Cases_on `array_bound` >>
  simp[type_memory_bytes_def, type_memory_size_def]
QED

Theorem type_memory_layout_list:
  !tys tvs tops cenv.
    EVERY type_memory_layout tys /\ struct_args_unique tops /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) tys tvs ==>
    MAP (type_memory_bytes cenv) tys = MAP type_memory_size tvs
Proof
  Induct_on `tys` >- (Cases_on `tvs` >> simp[]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  qmatch_goalsub_rename_tac
    `MAP (type_memory_bytes cenv) (head_ty::rest_tys) = MAP type_memory_size (head_tv::rest_tvs)` >>
  simp[] >> rpt strip_tac >>
  `type_memory_bytes cenv head_ty = type_memory_size head_tv` by
    (qpat_x_assum `type_memory_layout head_ty` (mp_tac o REWRITE_RULE [type_memory_layout_def]) >>
     disch_then (qspecl_then [`tops`, `cenv`, `head_tv`] mp_tac) >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem type_memory_layout_tuple:
  !tys. EVERY type_memory_layout tys ==> type_memory_layout (TupleT tys)
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [type_memory_layout_def] >>
  rpt strip_tac >> drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  drule_all type_memory_layout_list >> DISCH_TAC >>
  simp[type_memory_bytes_def, type_memory_size_def, type_memory_size_list_sum] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss []
QED

Theorem all_type_memory_layouts:
  (!ty. type_memory_layout ty) /\ (!tys. EVERY type_memory_layout tys)
Proof
  ho_match_mp_tac
    (legacyInduction.mutual_ind_from_ops
       (TypeBase.set_induction_of ``:type``)) >>
  simp[type_memory_layout_base, type_memory_layout_struct, type_memory_layout_flag,
    type_memory_layout_none, type_memory_layout_array, type_memory_layout_tuple]
QED

Theorem type_memory_bytes_evaluated:
  !tops cenv ty tv.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv
Proof
  rpt strip_tac >> mp_tac (Q.SPEC `ty` (CONJUNCT1 all_type_memory_layouts)) >>
  PURE_REWRITE_TAC [type_memory_layout_def] >>
  disch_then (qspecl_then [`tops`, `cenv`, `tv`] mp_tac) >> simp[]
QED

Theorem checked_compile_env_type_memory_bytes:
  !tops in_deploy layouts addr art vis mut name args ret stmts use_transient ty tv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    evaluate_type (type_env tops) ty = SOME tv ==>
    type_memory_bytes (build_compile_env tops vis mut name args ret stmts use_transient) ty =
      type_memory_size tv
Proof
  rpt strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  irule type_memory_bytes_evaluated >> qexists_tac `tops` >>
  simp[build_compile_env_ce_struct_fields]
QED
