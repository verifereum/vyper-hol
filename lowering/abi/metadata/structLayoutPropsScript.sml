(* TOP-LEVEL: actual struct metadata preserves declarations and assigns each
   evaluable field its source footprint, including forward references.
   Helpers expose the shape-preserving size-resolution pass. *)
Theory structLayoutProps
Ancestors
  compileVyper compileEnv vyperContext vyperValue finite_map list pair combin

Theorem resolve_struct_field_sizes_names:
  !tenv fields.
    MAP FST (resolve_struct_field_sizes tenv fields) = MAP FST fields
Proof
  rpt gen_tac >> simp[resolve_struct_field_sizes_def, MAP_MAP_o, o_DEF, LAMBDA_PROD] >>
  irule MAP_CONG >> simp[FORALL_PROD]
QED

Theorem resolve_struct_field_sizes_types:
  !tenv fields.
    MAP (FST o SND) (resolve_struct_field_sizes tenv fields) = MAP (FST o SND) fields
Proof
  rpt gen_tac >> simp[resolve_struct_field_sizes_def, MAP_MAP_o, o_DEF, LAMBDA_PROD] >>
  irule MAP_CONG >> simp[FORALL_PROD]
QED

Theorem resolve_struct_field_sizes_every:
  !P tenv fields.
    EVERY (P o FST o SND) (resolve_struct_field_sizes tenv fields) =
      EVERY (P o FST o SND) fields
Proof
  rpt gen_tac >>
  mp_tac (AP_TERM ``EVERY (P:type -> bool)``
    (Q.SPECL [`tenv`, `fields`] resolve_struct_field_sizes_types)) >>
  simp[EVERY_MAP, o_DEF]
QED

Theorem resolve_struct_field_sizes_metadata_every:
  !P tenv sf.
    FEVERY (\(name,fields). EVERY (P o FST o SND) fields)
      (resolve_struct_field_sizes tenv o_f sf) =
    FEVERY (\(name,fields). EVERY (P o FST o SND) fields) sf
Proof
  simp[FEVERY_DEF, resolve_struct_field_sizes_every]
QED

Theorem resolve_struct_field_size:
  !tenv fields name ty byte_count tv.
    MEM (name,ty,byte_count) (resolve_struct_field_sizes tenv fields) /\
    evaluate_type tenv ty = SOME tv ==> byte_count = type_memory_size tv
Proof
  simp[resolve_struct_field_sizes_def, MEM_MAP, EXISTS_PROD] >> rpt strip_tac >> gvs[]
QED

Theorem resolve_struct_field_sizes_typed:
  !fields tvs tenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP (FST o SND) fields) tvs ==>
    MAP (SND o SND) (resolve_struct_field_sizes tenv fields) = MAP type_memory_size tvs
Proof
  Induct_on `fields`
  >- (Cases_on `tvs` >> simp[resolve_struct_field_sizes_def]) >>
  rpt gen_tac >> qmatch_goalsub_rename_tac `resolve_struct_field_sizes _ (field_entry::rest_fields)` >>
  PairCases_on `field_entry` >> Cases_on `tvs` >>
  simp[resolve_struct_field_sizes_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[resolve_struct_field_sizes_def]
QED

Theorem make_struct_fields_map_sizes:
  !tops struct_name fields tvs.
    FLOOKUP (make_struct_fields_map tops) struct_name = SOME fields /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
      (MAP (FST o SND) fields) tvs ==>
    MAP (SND o SND) fields = MAP type_memory_size tvs
Proof
  rpt gen_tac >> simp[make_struct_fields_map_def, FLOOKUP_o_f, AllCaseEqs()] >>
  rpt strip_tac >> gvs[resolve_struct_field_sizes_types] >>
  drule_all resolve_struct_field_sizes_typed >> simp[]
QED

Theorem make_struct_fields_map_field_size:
  !tops struct_name fields field_name ty byte_count tv.
    FLOOKUP (make_struct_fields_map tops) struct_name = SOME fields /\
    MEM (field_name,ty,byte_count) fields /\
    evaluate_type (type_env tops) ty = SOME tv ==> byte_count = type_memory_size tv
Proof
  rpt gen_tac >> simp[make_struct_fields_map_def, FLOOKUP_o_f, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> drule_all resolve_struct_field_size >> simp[]
QED

Theorem build_compile_env_struct_field_size:
  !tops vis mut name args ret stmts use_transient struct_name fields field_name ty byte_count tv.
    FLOOKUP (build_compile_env tops vis mut name args ret stmts use_transient).ce_struct_fields
      struct_name = SOME fields /\ MEM (field_name,ty,byte_count) fields /\
    evaluate_type (type_env tops) ty = SOME tv ==> byte_count = type_memory_size tv
Proof
  simp[build_compile_env_ce_struct_fields] >> rpt strip_tac >>
  drule_all make_struct_fields_map_field_size >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source struct-layout theorem: " ^ name)
  end) (DB.thms "structLayoutProps")
