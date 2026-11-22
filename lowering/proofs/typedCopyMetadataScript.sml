(* Producer preparation: source declaration metadata is never an assumed
   compilation-environment invariant. Numeric field sizes are left untouched.
   TOP-LEVEL: make_struct_fields_map_acyclic,
     build_compile_env_struct_metadata_acyclic.
   Helpers: shallow_copy_type, shallow_copy_metadata_acyclic,
     nested_type_rank_metadata_invariant, nested_fields_rank,
     nested_copy_metadata_acyclic. *)
Theory typedCopyMetadata
Ancestors
  typedCopyDomain compileVyper compileEnv structLayoutProps supportedTypes supportedDecls
  checkedTypeNamespace supportedStmtTraverse
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
  MAP (FST o SND) (build_struct_fields_one tenv args) = MAP SND args
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

Theorem make_struct_fields_origin:
  !tops name fields.
    FLOOKUP (make_struct_fields_map tops) name = SOME fields ==>
    ?args. MEM (StructDecl name args) tops /\ MAP (FST o SND) fields = MAP SND args
Proof
  rpt gen_tac >> simp[make_struct_fields_map_def] >>
  rpt strip_tac >> drule built_struct_fields_origin >> simp[]
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

(* ===== Nested metadata and fuel-bounded rank invariance ===== *)

(* Missing entries are allowed, so this invariant survives rank's internal
   metadata deletions. Only field types matter, not their numeric sizes. *)
Definition struct_metadata_types_match_def:
  struct_metadata_types_match tops sf <=>
    !name fields args.
      FLOOKUP sf name = SOME fields /\
      supported_struct_fields tops (NONE,name) = SOME args ==>
      MAP (FST o SND) fields = MAP SND args
End

Theorem struct_metadata_types_match_delete:
  struct_metadata_types_match tops sf ==>
  struct_metadata_types_match tops (sf \\ name)
Proof
  simp[struct_metadata_types_match_def, DOMSUB_FLOOKUP_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem make_struct_fields_map_types_match:
  struct_args_unique tops ==>
  struct_metadata_types_match tops (make_struct_fields_map tops)
Proof
  rw[struct_metadata_types_match_def] >>
  drule supported_struct_fields_origin >> strip_tac >>
  fs[make_struct_fields_map_def] >> drule built_struct_fields_origin >>
  strip_tac >> gvs[] >> fs[struct_args_unique_def] >> metis_tac[]
QED

(* Agreement is needed only on names resolvable within the current budget.
   Including smaller budgets avoids imposing any arbitrary global depth. *)
Definition nested_metadata_agrees_def:
  nested_metadata_agrees tops sf sub fuel <=>
    !n name.
      n <= fuel /\
      supported_nested_type supported_scalar_type n tops
        (StructT (NONE,name)) ==>
      FLOOKUP sub name = FLOOKUP sf name
End

Theorem nested_metadata_agrees_delete:
  nested_metadata_agrees tops sf sub fuel /\ smaller <= fuel ==>
  nested_metadata_agrees tops (sf \\ name) (sub \\ name) smaller
Proof
  rw[nested_metadata_agrees_def, DOMSUB_FLOOKUP_THM] >>
  rw[] >> first_x_assum irule >> qexists_tac `n` >> simp[] >> decide_tac
QED

Theorem nested_metadata_fields:
  struct_metadata_types_match tops sf /\ supported_main_nsid nsid /\
  supported_nested_type supported_scalar_type fuel tops (StructT nsid) ==>
  0 < fuel /\
  EVERY (supported_nested_type supported_scalar_type (fuel - 1) tops o
         FST o SND) (get_struct_fields sf (nsid_to_string nsid))
Proof
  PairCases_on `nsid` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def, supported_main_nsid_def] >>
  strip_tac >> gvs[nsid_to_string_def] >>
  Cases_on `supported_struct_fields tops (NONE,nsid1)` >> gvs[] >>
  simp[get_struct_fields_def] >>
  Cases_on `FLOOKUP sf nsid1` >> simp[] >>
  fs[struct_metadata_types_match_def] >> res_tac >>
  fs[GSYM EVERY_MAP, MAP_MAP_o, o_DEF]
QED

Theorem nested_metadata_agrees_fields:
  nested_metadata_agrees tops sf sub fuel /\ supported_main_nsid nsid /\
  supported_nested_type supported_scalar_type fuel tops (StructT nsid) ==>
  get_struct_fields sub (nsid_to_string nsid) =
  get_struct_fields sf (nsid_to_string nsid)
Proof
  PairCases_on `nsid` >> rw[nsid_to_string_def, supported_main_nsid_def] >>
  fs[nested_metadata_agrees_def] >>
  first_x_assum (qspecl_then [`fuel`, `nsid1`] mp_tac) >>
  simp[] >> rw[get_struct_fields_def]
QED

Theorem nested_type_rank_metadata_invariant:
  !sf ty sub fuel tops.
    struct_metadata_types_match tops sf /\
    struct_metadata_types_match tops sub /\
    supported_nested_type supported_scalar_type fuel tops ty /\
    unqualified_struct_metadata sf /\ supported_type_namespace ty /\
    nested_metadata_agrees tops sf sub fuel ==>
    type_rank sub ty = type_rank sf ty
Proof
  recInduct type_rank_ind >> rpt conj_tac
  >- simp[type_rank_def]
  >- (rpt strip_tac >> rename1 `ArrayT elem bd` >> Cases_on `bd` >>
      qpat_x_assum `supported_nested_type _ _ _ (ArrayT _ _)` mp_tac >>
      simp[Once supported_nested_type_def, supported_scalar_type_def,
           supported_word_type_def, supported_string_type_def] >> strip_tac >>
      fs[type_rank_def, supported_type_namespace_def] >>
      first_x_assum irule >> qexistsl_tac [`fuel`, `tops`] >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `supported_nested_type _ _ _ (TupleT _)` mp_tac >>
      simp[Once supported_nested_type_def, supported_scalar_type_def,
           supported_word_type_def, supported_string_type_def] >> strip_tac >>
      fs[type_rank_def, supported_type_namespace_def] >>
      `EVERY supported_type_namespace tys` by
        fs[supported_types_namespace_every] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >>
      conj_tac >- (fs[EVERY_MEM] >> res_tac) >>
      qexistsl_tac [`fuel`, `tops`] >> fs[EVERY_MEM] >> res_tac)
  >- (rpt strip_tac >>
      fs[supported_type_namespace_def, supported_main_nsid_def] >>
      drule_then (qspec_then `nsid_to_string nsid` assume_tac)
        unqualified_struct_metadata_lookup >>
      drule_all nested_metadata_fields >> strip_tac >>
      drule_all nested_metadata_agrees_fields >> strip_tac >>
      simp[type_rank_def] >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
      rpt strip_tac >> qmatch_goalsub_rename_tac `FST (SND triple)` >>
      first_x_assum irule >> simp[] >>
      conj_tac >- (fs[EVERY_MEM] >> res_tac) >>
      qexistsl_tac [`fuel - 1`, `tops`] >>
      simp[struct_metadata_types_match_delete] >>
      fs[EVERY_MEM] >> irule nested_metadata_agrees_delete >>
      qexists_tac `fuel` >> simp[])
  >- simp[type_rank_def]
  >> simp[type_rank_def]
QED

Theorem nested_metadata_agrees_delete_unreachable:
  ~(?n. n <= fuel /\
        supported_nested_type supported_scalar_type n tops
          (StructT (NONE,name))) ==>
  nested_metadata_agrees tops sf (sf \\ name) fuel
Proof
  rw[nested_metadata_agrees_def, DOMSUB_FLOOKUP_THM] >>
  rw[] >> metis_tac[]
QED

(* If a parent can itself be expanded within the field budget, expand it
   and use a smaller budget. Otherwise no field can reach its name, so
   deleting that name preserves every field rank. This also handles names
   blocked by an interface declaration, which never resolve as structs. *)
Theorem nested_fields_rank:
  !fuel tops sf name fields.
    struct_metadata_types_match tops sf /\ unqualified_struct_metadata sf /\
    FLOOKUP sf name = SOME fields /\
    EVERY (supported_nested_type supported_scalar_type fuel tops o
           FST o SND) fields ==>
    SUM (MAP (type_rank sf o FST o SND) fields) <
    type_rank sf (StructT (NONE,name))
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `?n. n <= fuel /\
    supported_nested_type supported_scalar_type n tops (StructT (NONE,name))`
  >- (pop_assum strip_assume_tac >>
      drule_all (SIMP_RULE std_ss [supported_main_nsid_def] (Q.INST [`nsid` |-> `(NONE,name)`] nested_metadata_fields)) >> strip_tac >>
      first_x_assum irule >> simp[] >>
      qexistsl_tac [`n - 1`, `tops`] >>
      gvs[get_struct_fields_def, nsid_to_string_def]) >>
  `nested_metadata_agrees tops sf (sf \\ name) fuel` by
    (irule nested_metadata_agrees_delete_unreachable >>
     first_assum ACCEPT_TAC) >>
  `EVERY (supported_type_namespace o FST o SND) fields` by
    (drule_then (qspec_then `name` mp_tac) unqualified_struct_metadata_lookup >>
     simp[get_struct_fields_def]) >>
  `MAP (type_rank (sf \\ name) o FST o SND) fields =
   MAP (type_rank sf o FST o SND) fields` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule nested_type_rank_metadata_invariant >>
     fs[EVERY_MEM] >>
     qexistsl_tac [`fuel`, `tops`] >>
     simp[struct_metadata_types_match_delete] >> res_tac) >>
  simp[type_rank_def, nsid_to_string_def, get_struct_fields_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> gvs[]
QED

Theorem nested_copy_metadata_acyclic:
  struct_metadata_types_match tops sf /\ unqualified_struct_metadata sf /\
  FEVERY (λ(name,fields).
    EVERY (supported_nested_type supported_scalar_type fuel tops o
           FST o SND) fields) sf ==>
  acyclic_struct_metadata sf
Proof
  rw[acyclic_struct_metadata_def, FEVERY_DEF] >>
  irule nested_fields_rank >> simp[FLOOKUP_DEF] >>
  qexistsl_tac [`fuel`, `tops`] >> simp[]
QED

(* The builder uses unique declarations with supported, unqualified field types. *)
Theorem make_struct_fields_map_acyclic:
  struct_args_unique tops /\ supported_declaration_headers tops /\
  (!name fields. MEM (StructDecl name fields) tops ==>
    EVERY (supported_type_namespace o SND) fields) ==>
  acyclic_struct_metadata (make_struct_fields_map tops)
Proof
  strip_tac >> irule nested_copy_metadata_acyclic >>
  conj_tac
  >- (simp[unqualified_struct_metadata_def, make_struct_fields_map_def] >>
      irule built_struct_fields_every >> simp[FEVERY_FEMPTY] >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`LENGTH tops`, `tops`] >>
  simp[make_struct_fields_map_types_match] >>
  simp[make_struct_fields_map_def] >> irule built_struct_fields_every >>
  simp[FEVERY_FEMPTY] >> rpt strip_tac >>
  fs[supported_declaration_headers_def, EVERY_MEM] >>
  res_tac >>
  fs[supported_declaration_header_def, supported_place_type_def, EVERY_MEM]
QED

(* Regression: forward references, arrays of tuples, and non-word fields
   exercise the nested producer rather than the old shallow whitelist. *)
Theorem make_nested_struct_fields_acyclic_probe:
  acyclic_struct_metadata (make_struct_fields_map
    [StructDecl "Outer"
       [("items", ArrayT (TupleT [StructT (NONE,"Inner");
                                 BaseT (StringT 33)]) (Fixed 2))];
     StructDecl "Inner"
       [("values", ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 3))]])
Proof
  irule make_struct_fields_map_acyclic >> EVAL_TAC >> rw[] >>
  gvs[supported_type_namespace_def, supported_main_nsid_def]
QED

Theorem build_compile_env_struct_metadata_acyclic:
  struct_args_unique tops /\ supported_declaration_headers tops /\
  (!name fields. MEM (StructDecl name fields) tops ==>
    EVERY (supported_type_namespace o SND) fields) ==>
  acyclic_struct_metadata
    (build_compile_env tops vis mut name args ret stmts use_transient).ce_struct_fields
Proof
  simp[build_compile_env_ce_struct_fields] >> strip_tac >>
  drule_all make_struct_fields_map_acyclic >> simp[]
QED
