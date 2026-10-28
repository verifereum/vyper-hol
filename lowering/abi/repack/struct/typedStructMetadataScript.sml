(* TOP-LEVEL: a complete checked struct type yields its actual field
   metadata, distinct names, semantic field evaluations and physical strides. *)
Theory typedStructMetadata
Ancestors
  typedStructNames typedStructSizes structSourceProps typedCopyProducer
  typeLayoutProps vyperTypeABI vyperTypeExprSoundness
  context compileEnv compileVyper vyperContext vyperValue vyperTypeContract
  finite_map list pair combin

Theorem evaluate_type_struct_fields:
  !tenv nsid tv.
    evaluate_type tenv (StructT nsid) = SOME tv ==>
    ?args tvs. FLOOKUP tenv nsid = SOME (StructArgs args) /\
      evaluate_types (tenv \\ nsid) (MAP SND args) [] = SOME tvs /\
      tv = StructTV (ZIP (MAP FST args,tvs))
Proof
  rw[Once evaluate_type_def, AllCaseEqs(), LET_THM] >> simp[]
QED

Theorem evaluated_struct_copy_metadata:
  !tops in_deploy layouts addr art cenv nsid tv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) (StructT nsid) = SOME tv ==>
    ?fields tvs.
      get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid) = fields /\ tv = StructTV tvs /\
      ALL_DISTINCT (MAP FST fields) /\
      LIST_REL (\ty field_tv. evaluate_type (type_env tops) ty = SOME field_tv)
        (MAP (FST o SND) fields) (MAP SND tvs) /\
      EVERY (\entry. SND (SND entry) = type_memory_bytes cenv (FST (SND entry))) fields
Proof
  rpt gen_tac >> strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  drule evaluate_type_struct_fields >>
  disch_then (qx_choose_then `args` (qx_choose_then `field_tvs` strip_assume_tac)) >>
  drule (CONJUNCT2 evaluate_type_mono) >> DISCH_TAC >>
  qpat_assum `evaluate_types (type_env tops) (MAP SND args) [] = SOME field_tvs`
    (ASSUME_TAC o MATCH_MP evaluate_types_LIST_REL) >>
  `LENGTH (MAP FST args) = LENGTH field_tvs` by (drule LIST_REL_LENGTH >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `nsid`, `args`] evaluated_struct_metadata_types) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `fields` strip_assume_tac) >>
  `LIST_REL (\ty field_tv. evaluate_type (type_env tops) ty = SOME field_tv)
      (MAP (FST o SND) fields) field_tvs` by simp[] >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `nsid_to_string nsid`, `fields`]
    checked_struct_metadata_names_distinct) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `cenv`, `nsid_to_string nsid`, `fields`, `field_tvs`]
    checked_struct_metadata_sizes) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexistsl_tac [`fields`, `ZIP (MAP FST args,field_tvs)`] >>
  asm_simp_tac (srw_ss()) [get_struct_fields_def, MAP_ZIP]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed evaluated struct copy metadata: " ^ name)
  end) (DB.thms "typedStructMetadata")
