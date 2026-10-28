(*
 * Struct Field Map Properties
 *
 * The compile environment's struct field map (make_struct_fields_map) agrees
 * with the semantics' type environment (type_env) of the same program:
 *
 *   make_struct_fields_map_consistent — sfields_tenv_consistent holds
 *   make_struct_fields_map_memory_size — type_memory_bytes, which reads the
 *     map's field sizes, equals type_memory_size of the evaluated type
 *   build_compile_env_type_memory_bytes — the same at build_compile_env
 *)

Theory structFieldsProps
Ancestors
  compileVyper compileEnv typedCopyMetadata typedCopyProducer
  vyperTypeContract vyperTypeExprSoundness vyperContext vyperValue
  valueEncoding vfmConstants
  finite_map list pair combin

Theorem type_env_for_module_struct_mem:
  ∀tops src key args.
    FLOOKUP (type_env_for_module src tops) key = SOME (StructArgs args) ⇒
    ∃name. key = (src, name) ∧ MEM (StructDecl name args) tops
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases >> simp[type_env_for_module_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem type_env_for_module_struct_lookup:
  ∀tops name args.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ∧
    MEM (StructDecl name args) tops ⇒
    FLOOKUP (type_env_for_module NONE tops) (NONE, name) =
      SOME (StructArgs args)
Proof
  Induct >> simp[] >> Cases >>
  simp[type_env_for_module_def, type_def_keys_toplevel_def, FLOOKUP_UPDATE,
       ALL_DISTINCT_APPEND] >>
  rw[] >> gvs[] >> metis_tac[struct_decl_type_key_member]
QED

Theorem build_struct_fields_map_absent:
  ∀tops tenv sf name.
    (∀args. ¬MEM (StructDecl name args) tops) ⇒
    FLOOKUP (build_struct_fields_map tenv tops sf) name = FLOOKUP sf name
Proof
  Induct >> simp[build_struct_fields_map_def] >>
  Cases >> rw[build_struct_fields_map_def, FLOOKUP_UPDATE] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem build_struct_fields_map_lookup:
  ∀tops tenv sf name args.
    struct_args_unique tops ∧ MEM (StructDecl name args) tops ⇒
    FLOOKUP (build_struct_fields_map tenv tops sf) name =
      SOME (build_struct_fields_one tenv args)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `struct_args_unique tops` by (fs[struct_args_unique_def] >> metis_tac[MEM]) >>
  Cases_on `MEM (StructDecl name args) tops`
  >- (Cases_on `h` >> simp[build_struct_fields_map_def] >>
      first_x_assum irule >> fs[]) >>
  `h = StructDecl name args` by fs[] >>
  `∀a. ¬MEM (StructDecl name a) tops`
    by metis_tac[struct_args_unique_def, MEM] >>
  drule build_struct_fields_map_absent >>
  simp[build_struct_fields_map_def, FLOOKUP_UPDATE]
QED

Theorem built_struct_fields_names:
  MAP FST (build_struct_fields_one tenv args) = MAP FST args
Proof
  simp[build_struct_fields_one_def, MAP_MAP_o, o_DEF] >>
  irule MAP_CONG >> simp[FORALL_PROD]
QED

Theorem make_struct_fields_map_consistent:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ⇒
  sfields_tenv_consistent (make_struct_fields_map tops) (type_env tops)
Proof
  strip_tac >> drule distinct_type_keys_struct_args_unique >> strip_tac >>
  rw[sfields_tenv_consistent_def, make_struct_fields_map_def, type_env_def]
  >~ [`FLOOKUP (type_env_for_module NONE tops) _ = SOME (StructArgs _)`]
  >- (drule type_env_for_module_struct_mem >> strip_tac >>
      gvs[nsid_to_string_def] >> drule_all build_struct_fields_map_lookup >>
      simp[built_struct_fields_names, built_struct_fields_types]) >>
  drule built_struct_fields_origin >> simp[] >> strip_tac >>
  `fields = build_struct_fields_one (type_env_for_module NONE tops) args`
    by (drule_all build_struct_fields_map_lookup >>
        disch_then (qspecl_then [`type_env_for_module NONE tops`, `FEMPTY`]
                      mp_tac) >> gvs[]) >>
  qexistsl [`(NONE, name)`, `args`] >>
  gvs[type_env_for_module_struct_lookup, nsid_to_string_def,
      built_struct_fields_names, built_struct_fields_types]
QED

(* A struct's fields are evaluated without the struct itself in scope; the
   map sizes them against the whole environment, which gives the same
   types by evaluate_type_mono. *)
Theorem build_struct_fields_one_size:
  ∀args tvs.
    OPT_MMAP (evaluate_type (tenv \\ k)) (MAP SND args) = SOME tvs ⇒
    SUM (MAP (SND o SND) (build_struct_fields_one tenv args)) =
      type_memory_size_fields (ZIP (MAP FST args, tvs))
Proof
  Induct >> simp[build_struct_fields_one_def, type_memory_size_def] >>
  Cases >> rw[] >> gvs[build_struct_fields_one_def, type_memory_size_def] >>
  imp_res_tac evaluate_type_mono >> simp[field_mem_bytes_def]
QED

Theorem tuple_memory_bytes_size:
  ∀tys tvs.
    (∀ty tv. MEM ty tys ∧ evaluate_type tenv ty = SOME tv ⇒
             type_memory_bytes cenv ty = type_memory_size tv) ∧
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs ⇒
    SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs
Proof
  Induct >> rw[] >> gvs[type_memory_size_def] >>
  rename1 `evaluate_type tenv h = SOME tv0` >>
  qpat_x_assum `∀ty tv. _` (qspecl_then [`h`, `tv0`] mp_tac) >> simp[]
QED

Theorem make_struct_fields_map_memory_size:
  ∀cenv ty.
    struct_args_unique tops ∧
    cenv.ce_struct_fields = make_struct_fields_map tops ⇒
    ∀tv. evaluate_type (type_env tops) ty = SOME tv ⇒
         type_memory_bytes cenv ty = type_memory_size tv
Proof
  ho_match_mp_tac type_memory_bytes_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
          type_memory_size_def, evaluate_types_OPT_MMAP] >>
      fs[type_env_def] >> drule type_env_for_module_struct_mem >>
      strip_tac >> gvs[nsid_to_string_def, get_struct_fields_def,
                       make_struct_fields_map_def] >>
      drule_all build_struct_fields_map_lookup >> simp[] >> strip_tac >>
      fs[GSYM type_env_def] >> drule build_struct_fields_one_size >>
      simp[])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
          type_memory_size_def, evaluate_types_OPT_MMAP] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule tuple_memory_bytes_size >>
      qexists_tac `type_env tops` >> simp[] >> metis_tac[])
  >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def,
      type_memory_size_def, word_size_def]
QED

Theorem build_compile_env_type_memory_bytes:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ∧
  evaluate_type (type_env tops) ty = SOME tv ⇒
  type_memory_bytes
    (build_compile_env tops vis mut func_name args ret_type fn_body use_trans) ty =
  type_memory_size tv
Proof
  strip_tac >> irule make_struct_fields_map_memory_size >>
  simp[build_compile_env_ce_struct_fields] >>
  metis_tac[distinct_type_keys_struct_args_unique]
QED
