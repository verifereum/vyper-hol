(* TOP-LEVEL: evaluated source structs have matching field declarations in
   the actual compiler metadata. Namespace uniqueness comes from the checker.
   Helpers establish lookup origins and completeness of the metadata builder. *)
Theory structSourceProps
Ancestors
  structLayoutProps typedCopyMetadata typedCopyProducer compileVyper compileEnv
  vyperContext vyperAST vyperValue vyperTypeContract finite_map pred_set list option pair

Theorem build_struct_fields_map_domain:
  !tops sf name.
    name IN FDOM (build_struct_fields_map tops sf) <=>
      name IN FDOM sf \/ ?args. MEM (StructDecl name args) tops
Proof
  Induct_on `tops` >- simp[build_struct_fields_map_def] >>
  rpt gen_tac >> qmatch_goalsub_rename_tac `build_struct_fields_map (top_decl::rest_tops) _` >>
  Cases_on `top_decl` >> simp[build_struct_fields_map_def] >> metis_tac[]
QED

Theorem type_env_for_module_struct_origin:
  !tops src nsid args.
    FLOOKUP (type_env_for_module src tops) nsid = SOME (StructArgs args) ==>
    ?name. nsid = (src,name) /\ MEM (StructDecl name args) tops
Proof
  Induct_on `tops` >- simp[type_env_for_module_def] >>
  rpt gen_tac >> qmatch_goalsub_rename_tac `type_env_for_module _ (top_decl::rest_tops)` >>
  Cases_on `top_decl` >> simp[type_env_for_module_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem make_struct_fields_lookup_exists:
  !tops name args.
    MEM (StructDecl name args) tops ==>
    ?fields. FLOOKUP (make_struct_fields_map tops) name = SOME fields
Proof
  rpt strip_tac >>
  `name IN FDOM (build_struct_fields_map tops FEMPTY)` by
    (simp[build_struct_fields_map_domain] >> goal_assum drule) >>
  simp[make_struct_fields_map_def, FLOOKUP_o_f, FLOOKUP_DEF]
QED

Theorem make_struct_fields_source_types:
  !tops name args.
    struct_args_unique tops /\ MEM (StructDecl name args) tops ==>
    ?fields. FLOOKUP (make_struct_fields_map tops) name = SOME fields /\
      MAP (FST o SND) fields = MAP SND args
Proof
  rpt strip_tac >> drule make_struct_fields_lookup_exists >> strip_tac >>
  drule make_struct_fields_origin >> strip_tac >>
  qexists_tac `fields` >> fs[struct_args_unique_def] >> metis_tac[]
QED

Theorem evaluated_struct_metadata_types:
  !tops nsid args.
    struct_args_unique tops /\ FLOOKUP (type_env tops) nsid = SOME (StructArgs args) ==>
    ?fields. FLOOKUP (make_struct_fields_map tops) (nsid_to_string nsid) = SOME fields /\
      MAP (FST o SND) fields = MAP SND args
Proof
  rpt strip_tac >> fs[type_env_def] >> drule type_env_for_module_struct_origin >>
  strip_tac >> gvs[nsid_to_string_def] >>
  drule_all make_struct_fields_source_types >> simp[]
QED

Theorem checked_struct_metadata_types:
  !tops in_deploy layouts addr art nsid args.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    FLOOKUP (type_env tops) nsid = SOME (StructArgs args) ==>
    ?fields. FLOOKUP (make_struct_fields_map tops) (nsid_to_string nsid) = SOME fields /\
      MAP (FST o SND) fields = MAP SND args
Proof
  rpt strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  drule_all evaluated_struct_metadata_types >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source struct-metadata theorem: " ^ name)
  end) (DB.thms "structSourceProps")
