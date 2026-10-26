(* Producer preparation: source declaration metadata is never an assumed
   compilation-environment invariant. Numeric field sizes are left untouched.
   TOP-LEVEL: shallow_copy_type, shallow_copy_metadata_acyclic. *)
Theory typedCopyMetadata
Ancestors
  typedCopyDomain compileVyper compileEnv supportedTypes supportedDecls
  vyperAST finite_map list pair combin arithmetic pred_set

Definition shallow_copy_type_def:
  shallow_copy_type sf (BaseT _) = T /\
  shallow_copy_type sf (ArrayT elem _) = shallow_copy_type sf elem /\
  shallow_copy_type sf (TupleT tys) = EVERY (shallow_copy_type sf) tys /\
  shallow_copy_type sf (StructT nsid) =
    EVERY (is_word_type o FST o SND)
      (get_struct_fields sf (nsid_to_string nsid)) /\
  shallow_copy_type sf (FlagT _) = T /\
  shallow_copy_type sf NoneT = T
Termination
  WF_REL_TAC `measure (type_size o SND)`
End

Theorem word_type_rank:
  is_word_type ty ==> type_rank sf ty = 1
Proof
  Cases_on `ty` >> simp[is_word_type_def, type_rank_def] >>
  Cases_on `b` >> simp[is_word_type_def, type_rank_def] >>
  Cases_on `b'` >> simp[is_word_type_def, type_rank_def]
QED

Theorem word_fields_rank:
  EVERY (is_word_type o FST o SND) fields ==>
  SUM (MAP (type_rank sf o FST o SND) fields) = LENGTH fields
Proof
  Induct_on `fields` >> simp[] >> rpt strip_tac >>
  drule word_type_rank >> disch_then (qspec_then `sf` assume_tac) >> gvs[]
QED

Theorem shallow_type_delete_rank:
  !sf ty name.
  shallow_copy_type sf ty /\
  (EVERY (is_word_type o FST o SND) (get_struct_fields sf name) ==>
   is_word_type ty) ==>
  type_rank (sf \\ name) ty = type_rank sf ty
Proof
  recInduct shallow_copy_type_ind >> simp[shallow_copy_type_def, type_rank_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> fs[is_word_type_def] >> first_x_assum irule >>
      fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >- (rpt strip_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
      rpt strip_tac >> fs[EVERY_MEM, is_word_type_def] >>
      first_x_assum irule >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >> rpt strip_tac >>
  `nsid_to_string nsid <> name` by (strip_tac >> gvs[is_word_type_def]) >>
  `get_struct_fields (sf \\ name) (nsid_to_string nsid) =
   get_struct_fields sf (nsid_to_string nsid)` by
    simp[get_struct_fields_def, DOMSUB_FLOOKUP_THM] >>
  simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  drule word_fields_rank >> disch_then (fn th => rewrite_tac[th])
QED

Theorem shallow_copy_metadata_acyclic:
  FEVERY (λ(name,fields). EVERY (shallow_copy_type sf o FST o SND) fields) sf ==>
  acyclic_struct_metadata sf
Proof
  simp[FEVERY_DEF, acyclic_struct_metadata_def] >> rpt strip_tac >>
  rename1 `name IN FDOM sf` >>
  `EVERY (shallow_copy_type sf o FST o SND) (get_struct_fields sf name)` by
    (simp[get_struct_fields_def, FLOOKUP_DEF] >> first_x_assum irule >> simp[]) >>
  `MAP (type_rank (sf \\ name) o FST o SND) (get_struct_fields sf name) =
   MAP (type_rank sf o FST o SND) (get_struct_fields sf name)` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule shallow_type_delete_rank >> fs[EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  simp[type_rank_def, nsid_to_string_def, get_struct_fields_def, FLOOKUP_DEF] >>
  fs[get_struct_fields_def, FLOOKUP_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> gvs[]
QED

Theorem built_struct_fields_types:
  MAP (FST o SND) (build_struct_fields_one sft args) = MAP SND args
Proof
  simp[build_struct_fields_one_def, MAP_MAP_o, o_DEF] >>
  irule MAP_CONG >> simp[FORALL_PROD]
QED

(* Every lookup in the actual metadata builder has a source declaration,
   or is inherited from its input map. Field sizes need not be guessed. *)
Theorem built_struct_fields_origin:
  !tops env sf name fields.
  FLOOKUP (build_struct_fields_map env tops sf) name = SOME fields ==>
  FLOOKUP sf name = SOME fields \/
  ?args. MEM (StructDecl name args) tops /\
         MAP (FST o SND) fields = MAP SND args
Proof
  Induct_on `tops` >> simp[build_struct_fields_map_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[build_struct_fields_map_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs(), built_struct_fields_types] >>
  metis_tac[]
QED

Theorem supported_struct_fields_origin:
  !tops name args.
  supported_struct_fields tops (NONE,name) = SOME args ==>
  MEM (StructDecl name args) tops
Proof
  Induct_on `tops` >> simp[supported_struct_fields_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[supported_struct_fields_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> metis_tac[]
QED

(* This is a source-namespace premise, not an environment premise. A typed
   contract's distinct type-definition keys imply it (including all flags
   and interfaces); duplicate struct names are NOT assumed harmless. *)
Definition struct_args_unique_def:
  struct_args_unique tops <=>
    !name args args'.
      MEM (StructDecl name args) tops /\ MEM (StructDecl name args') tops ==>
      args = args'
End

Theorem supported_word_type_is_word:
  supported_word_type ty ==> is_word_type ty
Proof
  Cases_on `ty` >> simp[supported_word_type_def, is_word_type_def] >>
  Cases_on `b` >> simp[supported_word_type_def, is_word_type_def] >>
  Cases_on `b'` >> simp[supported_word_type_def, is_word_type_def]
QED

Theorem supported_value_type_shallow_metadata:
  struct_args_unique tops /\ supported_value_type tops ty ==>
  shallow_copy_type (make_struct_fields_map tops) ty
Proof
  rpt strip_tac >>
  Cases_on `ty` >>
  fs[supported_value_type_def, supported_scalar_type_def,
     supported_word_type_def, supported_string_type_def, shallow_copy_type_def]
  >- (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      rename1 `supported_scalar_type elem ==> _` >>
      Cases_on `elem` >> simp[supported_scalar_type_def,
          supported_word_type_def, supported_string_type_def, shallow_copy_type_def])
  >- (rename1 `supported_word_type elem` >>
      qmatch_asmsub_rename_tac `bound_CASE bd` >>
      Cases_on `bd` >> gvs[] >> drule supported_word_type_is_word >> strip_tac >>
      Cases_on `elem` >> gvs[is_word_type_def, shallow_copy_type_def])
  >> rename1 `nsid_to_string nsid` >>
  Cases_on `supported_struct_fields tops nsid` >> gvs[] >>
  rename1 `supported_struct_fields tops nsid = SOME args` >>
  Cases_on `nsid` >>
  rename1 `supported_struct_fields tops (modid,name) = SOME args` >>
  Cases_on `modid` >> gvs[supported_struct_fields_other_module, nsid_to_string_def] >>
  drule supported_struct_fields_origin >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM triple (get_struct_fields (make_struct_fields_map tops) name)` >>
  Cases_on `FLOOKUP (make_struct_fields_map tops) name` >>
  gvs[get_struct_fields_def] >>
  fs[make_struct_fields_map_def] >> drule built_struct_fields_origin >>
  strip_tac >> gvs[] >>
  fs[struct_args_unique_def] >>
  rename1 `MEM (StructDecl name found_args) tops` >>
  `found_args = args` by metis_tac[] >> gvs[EVERY_MEM] >>
  `MEM (FST (SND triple)) (MAP SND args)` by
    (qpat_x_assum `MAP (FST o SND) _ = MAP SND _`
       (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists_tac `triple` >> simp[]) >>
  fs[MEM_MAP] >> metis_tac[supported_word_type_is_word]
QED

Theorem built_struct_fields_every:
  FEVERY (λ(name,fields). EVERY (P o FST o SND) fields) sf /\
  (!name args. MEM (StructDecl name args) tops ==> EVERY (P o SND) args) ==>
  FEVERY (λ(name,fields). EVERY (P o FST o SND) fields)
    (build_struct_fields_map env tops sf)
Proof
  simp[FEVERY_DEF] >> rpt strip_tac >>
  rename1 `name IN FDOM (build_struct_fields_map env tops sf)` >>
  `FLOOKUP (build_struct_fields_map env tops sf) name =
   SOME ((build_struct_fields_map env tops sf) ' name)` by simp[FLOOKUP_DEF] >>
  drule built_struct_fields_origin >> strip_tac
  >- (fs[FLOOKUP_DEF] >>
      qpat_x_assum `sf ' name = _` (SUBST1_TAC o SYM) >>
      first_x_assum irule >> simp[])
  >> `EVERY (P o SND) args` by metis_tac[] >>
  `EVERY P (MAP SND args)` by fs[EVERY_MAP, o_DEF] >>
  qpat_x_assum `MAP (FST o SND) _ = MAP SND _` (SUBST_ALL_TAC o SYM) >>
  fs[EVERY_MAP, o_DEF]
QED

(* Producer for the actual builder. The two source premises are checkable:
   namespace uniqueness and the supported declaration whitelist. No premise
   assumes anything about a compile_env, ranks, or termination. *)
Theorem make_struct_fields_map_acyclic:
  struct_args_unique tops /\ supported_declaration_headers tops ==>
  acyclic_struct_metadata (make_struct_fields_map tops)
Proof
  strip_tac >> irule shallow_copy_metadata_acyclic >>
  simp[make_struct_fields_map_def] >> irule built_struct_fields_every >>
  simp[FEVERY_FEMPTY] >> rpt strip_tac >>
  `EVERY (supported_value_type tops o SND) args` by
    (fs[supported_declaration_headers_def, EVERY_MEM] >>
     first_x_assum drule >> simp[supported_declaration_header_def, EVERY_MEM]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  ONCE_REWRITE_TAC [GSYM make_struct_fields_map_def] >>
  irule supported_value_type_shallow_metadata >> simp[] >> fs[EVERY_MEM]
QED

Theorem build_compile_env_struct_metadata_acyclic:
  struct_args_unique tops /\ supported_declaration_headers tops ==>
  acyclic_struct_metadata
    (build_compile_env tops vis mut name args ret stmts use_transient).ce_struct_fields
Proof
  simp[build_compile_env_ce_struct_fields] >> strip_tac >>
  irule make_struct_fields_map_acyclic >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("TYPED_COPY_METADATA_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("Typed-copy metadata fact not kernel closed: " ^ n)
  end) (DB.thms "typedCopyMetadata");
