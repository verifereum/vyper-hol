(* Shared event metadata and pure argument readiness for the Log cases. *)
Theory bodySimLogArgs
Ancestors bodyCallSupport bodySingletonCallSupport
  allocLimits allocLimitsProps
  exprSimSource bodyExprPreFacts exprSimHypsDefs list bodySim stmtSimLog exprSimHyps
  bodyStorageCases bodyInvSplit bodyInvCodeProps bodyInvExecutionProps
  bodyInvMetadataProps bodyMainModuleProps compileUnit alist
  compileEnv compileVyper supportedStmts supportedDecls supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperEvent vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness exprLowering
  vyperValue valueEncodingProps placeMemoryTypeInterfaces structFieldsProps exprSimProps arithmetic
  aggregateEvaluatedLayout valueCopyBytes vyperEventArgCompat checkedTypeNamespace
  vyperTypeExprResult retAbiPlanProps abiDecoderMembers finite_map pred_set

(* Expression readiness comes directly from exprSimSource; the statement
   dispatcher is not needed here. *)
(* ===== The event's metadata ===== *)

Theorem log_type_env_namespace[local]:
  !tops src sid name a.
    FLOOKUP (type_env_for_module src tops) (sid,name) = SOME a ==> sid = src
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases >> simp[type_env_for_module_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem module_type_env_submap:
  !mods src tops. ALOOKUP mods src = SOME tops ==>
    type_env_for_module src tops SUBMAP type_env_all_modules mods
Proof
  Induct >> simp[type_env_all_modules_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h0 = src` >>
  gvs[type_env_all_modules_def, finite_mapTheory.SUBMAP_FLOOKUP_EQN,
      finite_mapTheory.FLOOKUP_FUNION] >>
  rpt strip_tac >> PairCases_on `x` >>
  drule log_type_env_namespace >> strip_tac >> gvs[] >>
  Cases_on `FLOOKUP (type_env_for_module h0 h1) (src,x1)`
  >- (gvs[] >> metis_tac[]) >>
  drule log_type_env_namespace >> simp[]
QED

Theorem body_log_runtime_struct_namespace[local]:
  !tops ctx cenv cx k a.
    body_inv tops ctx cenv cx /\
    FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE
Proof
  rpt strip_tac >> PairCases_on `k` >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_type_env >>
  fs[type_env_all_modules_def, FLOOKUP_FUNION] >>
  metis_tac[log_type_env_namespace]
QED

Theorem body_main_type_env_submap:
  !cx tops. get_module_code cx NONE = SOME tops ==>
    type_env tops SUBMAP get_tenv cx
Proof
  rw[get_module_code_def, get_tenv_def, type_env_def, AllCaseEqs()] >>
  simp[module_type_env_submap]
QED

Theorem supported_nested_abi_env:
  !leaf fuel tops ty.
    (!t. leaf t ==> supported_event_leaf_type t) ==>
    !large removed.
      supported_nested_type leaf fuel tops ty /\ type_env tops SUBMAP large /\
      (!k fields. FLOOKUP large k = SOME (StructArgs fields) ==> FST k = NONE) ==>
      vyper_to_abi_type (DRESTRICT (type_env tops) (COMPL removed)) ty =
      vyper_to_abi_type (DRESTRICT large (COMPL removed)) ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `leaf ty`
  >- (`supported_event_leaf_type ty` by metis_tac[] >>
      Cases_on `ty` >>
      gvs[supported_event_leaf_type_def, supported_scalar_type_def,
          supported_word_type_def, supported_string_type_def]) >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  Cases_on `ty` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac
  >~ [`FLOOKUP _ p`]
  >- (Cases_on `FST p = NONE`
      >| [ALL_TAC,
          PairCases_on `p` >> Cases_on `p0` >> gvs[] >>
          Cases_on `(SOME x,p1) IN removed` >>
          gvs[type_env_qualified_lookup, FLOOKUP_DRESTRICT] >>
          Cases_on `FLOOKUP large (SOME x,p1)` >> gvs[] >>
          Cases_on `x'` >> gvs[] >> res_tac >> gvs[]] >>
      Cases_on `supported_struct_fields tops p` >> gvs[] >>
      rename1 `supported_struct_fields tops p = SOME fields` >>
      drule supported_struct_fields_type_env >> strip_tac >>
      `FLOOKUP large p = SOME (StructArgs fields)` by
        metis_tac[FLOOKUP_SUBMAP] >>
      Cases_on `p IN removed` >>
      simp[FLOOKUP_DRESTRICT] >>
      simp[DRESTRICT_DOMSUB, vyper_to_abi_types_MAP] >>
      `COMPL removed DELETE p = COMPL (p INSERT removed)` by
        (simp[EXTENSION] >> metis_tac[]) >>
      asm_rewrite_tac[] >> irule MAP_CONG >>
      gvs[EVERY_MEM, combinTheory.o_DEF, MEM_MAP, PULL_EXISTS] >>
      metis_tac[])
  >~ [`vyper_to_abi_types _ tys`]
  >- (gvs[vyper_to_abi_types_MAP, EVERY_MEM] >>
      irule MAP_CONG >> simp[] >> metis_tac[]) >>
  Cases_on `b` >> gvs[] >> metis_tac[]
QED

Theorem supported_nested_evaluated_assignable:
  !leaf fuel tops ty.
    (!t. leaf t ==> supported_event_leaf_type t) ==>
    !large removed tv.
      supported_nested_type leaf fuel tops ty /\ type_env tops SUBMAP large /\
      (!k fields. FLOOKUP large k = SOME (StructArgs fields) ==> FST k = NONE) /\
      evaluate_type (DRESTRICT large (COMPL removed)) ty = SOME tv ==>
      assignable_type (DRESTRICT large (COMPL removed)) ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `leaf ty`
  >- (`supported_event_leaf_type ty` by metis_tac[] >>
      Cases_on `ty = BaseT (BytesT (Fixed 0))`
      >- gvs[supported_event_leaf_type_def, supported_scalar_type_def,
             supported_word_type_def, supported_string_type_def] >>
      Cases_on `ty` >>
      gvs[supported_event_leaf_type_def, supported_scalar_type_def,
          supported_word_type_def, supported_string_type_def] >>
      simp[assignable_type_def, well_formed_type_def]) >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  Cases_on `ty` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac
  >~ [`assignable_type _ (TupleT tys)`]
  >- (`well_formed_type (DRESTRICT large (COMPL removed)) (TupleT tys)` by
        simp[well_formed_type_def] >>
      simp[assignable_type_def, GSYM NULL_EQ] >>
      gvs[vyperValueTheory.evaluate_type_def,
          vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
      `EVERY IS_SOME (MAP (evaluate_type (DRESTRICT large (COMPL removed))) tys)` by
        (simp[GSYM IS_SOME_OPT_MMAP] >>
         Cases_on `OPT_MMAP (evaluate_type (DRESTRICT large (COMPL removed))) tys` >>
         gvs[]) >>
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, optionTheory.IS_SOME_EXISTS] >> metis_tac[])
  >~ [`assignable_type _ (ArrayT elem bd)`]
  >- (`well_formed_type (DRESTRICT large (COMPL removed)) (ArrayT elem bd)` by
        simp[well_formed_type_def] >>
      simp[assignable_type_def] >> Cases_on `bd` >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `FST p = NONE`
  >| [ALL_TAC,
      gvs[vyperValueTheory.evaluate_type_def, FLOOKUP_DRESTRICT, AllCaseEqs()] >>
      metis_tac[]] >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  rename1 `supported_struct_fields tops p = SOME fields` >>
  drule supported_struct_fields_type_env >> strip_tac >>
  `FLOOKUP large p = SOME (StructArgs fields)` by metis_tac[FLOOKUP_SUBMAP] >>
  `well_formed_type (DRESTRICT large (COMPL removed)) (StructT p)` by
    simp[well_formed_type_def] >>
  Cases_on `p IN removed` >>
  gvs[vyperValueTheory.evaluate_type_def, FLOOKUP_DRESTRICT] >>
  simp[assignable_type_def, FLOOKUP_DRESTRICT, GSYM NULL_EQ] >>
  gvs[DRESTRICT_DOMSUB, vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  `COMPL removed DELETE p = COMPL (p INSERT removed)` by
    (simp[EXTENSION] >> metis_tac[]) >>
  gvs[] >>
  `EVERY IS_SOME
     (MAP (evaluate_type (DRESTRICT large (COMPL (p INSERT removed))))
          (MAP SND fields))` by
    (simp[GSYM IS_SOME_OPT_MMAP] >>
     Cases_on `OPT_MMAP (evaluate_type (DRESTRICT large (COMPL (p INSERT removed))))
                  (MAP SND fields)` >> gvs[]) >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, combinTheory.o_DEF,
      optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem supported_place_evaluated_assignable:
  !tops tenv ty tv.
    supported_place_type tops ty /\ type_env tops SUBMAP tenv /\
    (!k fields. FLOOKUP tenv k = SOME (StructArgs fields) ==> FST k = NONE) /\
    evaluate_type tenv ty = SOME tv ==>
    assignable_type tenv ty
Proof
  rpt strip_tac >>
  qspecl_then [`supported_scalar_type`, `LENGTH tops`, `tops`, `ty`]
    mp_tac supported_nested_evaluated_assignable >>
  simp[supported_event_leaf_type_def] >>
  disch_then (qspecl_then [`tenv`, `{}`, `tv`] mp_tac) >>
  gvs[supported_place_type_def, DRESTRICT_UNIV]
QED

Theorem supported_place_abi_env:
  !tops cx ty.
    get_module_code cx NONE = SOME tops /\ supported_place_type tops ty /\
    (!k fields. FLOOKUP (get_tenv cx) k = SOME (StructArgs fields) ==> FST k = NONE) ==>
    vyper_to_abi_type (type_env tops) ty = vyper_to_abi_type (get_tenv cx) ty
Proof
  rpt strip_tac >> drule body_main_type_env_submap >> strip_tac >>
  qspecl_then [`supported_scalar_type`, `LENGTH tops`, `tops`, `ty`]
    mp_tac supported_nested_abi_env >>
  simp[supported_place_type_def, supported_event_leaf_type_def] >>
  disch_then (qspecl_then [`get_tenv cx`, `{}`] mp_tac) >>
  gvs[supported_place_type_def, DRESTRICT_UNIV]
QED

Theorem supported_event_fields_some[local]:
  !tops id fields.
    supported_event_fields tops id = SOME fields ==>
    ?name. id = (NONE, name) /\ MEM (EventDecl name fields) tops /\
           !tenv. lookup_event_metadata_in tenv name tops =
                  SOME (event_hash tenv name (MAP (SND o FST) fields),
                        MAP (SND o FST) fields, MAP SND fields)
Proof
  Induct >> simp[supported_event_fields_def] >>
  rpt gen_tac >> PairCases_on `id` >>
  simp[supported_event_fields_def] >>
  Cases_on `id0` >> simp[] >> strip_tac >>
  Cases_on `h` >> fs[lookup_event_metadata_in_def, AllCaseEqs()] >>
  rw[] >> res_tac >> fs[]
QED

Theorem event_decl_names_mem[local]:
  !tops n a. MEM (EventDecl n a) tops ==> MEM n (supported_event_names tops)
Proof
  Induct >> simp[supported_event_names_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `h` >> simp[] >> metis_tac[]
QED

Theorem event_names_unique[local]:
  !tops n. ALL_DISTINCT (supported_event_names tops) ==> event_decl_unique n tops
Proof
  Induct >> simp[event_decl_unique_def, supported_event_names_def] >>
  Cases >> simp[] >> fs[event_decl_unique_def] >>
  metis_tac[event_decl_names_mem]
QED

(* Both metadata lookups resolve the same declaration and its event hash. *)
Theorem body_log_aggregate_metadata:
  !tops ctx cenv cx id fields.
    body_inv tops ctx cenv cx /\ supported_event_fields tops id = SOME fields ==>
    ?h. cenv.ce_event_info (nsid_to_string id) =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        LENGTH (FILTER I (MAP SND fields)) <= 3 /\
        EVERY (\f. if SND f then supported_event_leaf_type (SND (FST f))
                    else supported_nested_type supported_event_leaf_type
                           (LENGTH tops) tops (SND (FST f))) fields
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_event_fields_some >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_type_env >>
  `get_tenv cx = type_env tops` by
    fs[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE)` by
    fs[contract_inv_def, build_event_info_mods_singleton,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  `EVERY (\f. if SND f then supported_event_leaf_type (SND (FST f))
              else supported_nested_type supported_event_leaf_type
                     (LENGTH tops) tops (SND (FST f))) fields /\
   LENGTH (FILTER I (MAP SND fields)) <= 3` by
    (gvs[supported_program_def,
         supported_declaration_headers_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e tops ==> supported_declaration_header _ _` drule >>
     simp[supported_declaration_header_def, EVERY_MEM]) >>
  `event_decl_unique name tops` by
    gvs[supported_program_def,
        supported_declaration_names_def, event_names_unique] >>
  gvs[nsid_to_string_def, build_event_info_lookup_event_metadata_in,
      lookup_event_metadata_def, get_module_code_def, AllCaseEqs(), event_hash_def]
QED

Theorem body_log_metadata:
  !tops ctx cenv cx id fields.
    body_inv tops ctx cenv cx /\ supported_event_fields tops id = SOME fields /\
    EVERY supported_scalar_type (MAP (SND o FST) fields) ==>
    ?h. cenv.ce_event_info (nsid_to_string id) =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        LENGTH (FILTER I (MAP SND fields)) <= 3 /\
        EVERY supported_scalar_type (MAP (SND o FST) fields)
Proof
  rpt strip_tac >>
  drule_all body_log_aggregate_metadata >> metis_tac[]
QED

(* ===== The arguments ===== *)

Theorem log_arg_body_pre[local]:
  !tops ctx cenv cx env e calls es.
    body_stmt_safe tops (Expr e) /\ ~is_extcode e /\
    body_inv tops ctx cenv cx /\ supported_effect_free_expr tops e /\
    ~supported_expr_exists (const_name_root cx) e /\
    well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) e /\
    alloc_limits_expr cenv e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    simp[supported_expr_def, supported_effect_free_pure] >>
  drule_all_then strip_assume_tac supported_singleton_expr_body_calls >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_type_env >>
  `get_tenv cx = type_env tops` by
    fs[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es`, `calls`]
    irule stmt_expr_body_pre >>
  simp[] >> qexists_tac `calls` >> first_assum ACCEPT_TAC
QED

Theorem body_log_snapshot_expr_pre_mods:
  EVERY (\e. ~is_extcode e) args /\
  contract_inv mods exps ctx cenv cx /\ supported_pure_exprs (main_module mods) args /\
  well_typed_exprs env args /\
  ~supported_exprs_exists
     (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) args /\
  alloc_limits_exprs cenv args /\
  ~supported_exprs_exists (const_name_root_mods mods) args /\
  call_evaluation_safe cx (int_calls_exprs args) /\
  (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
            occurs_abi_decode_target target (main_module mods)) ==>
  !e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st /\
    ~supported_expr_exists (unallocated_bare_global_root cenv env) e ==>
    expr_body_pre_mods mods cenv cx env e st
Proof
  rpt strip_tac >>
  `supported_pure_expr (main_module mods) e /\ ~is_extcode e /\
   ~supported_expr_exists (const_name_root_mods mods) e /\
   ~supported_expr_exists
     (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) e /\
   (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
      occurs_abi_decode_target target (main_module mods))` by
    (fs[supported_pure_exprs_every, EVERY_MEM, supported_exprs_exists_every,
        EXISTS_MEM] >> metis_tac[]) >>
  `supported_expr (main_module mods) e` by simp[supported_expr_def] >>
  `alloc_limits_expr cenv e` by metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem] >>
  mp_tac (Q.INST [`calls` |-> `[]`, `es` |-> `st`] stmt_expr_body_pre_main_mods) >>
  simp[] >> metis_tac[well_typed_exprs_member, call_evaluation_safe_exprs_mem]
QED

Theorem body_log_snapshot_expr_pre:
  EVERY (\e. ~is_extcode e) args /\
  body_inv tops ctx cenv cx /\ supported_pure_exprs tops args /\
  well_typed_exprs env args /\
  ~supported_exprs_exists
     (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) args /\
  alloc_limits_exprs cenv args /\
  ~supported_exprs_exists (const_name_root cx) args /\
  call_evaluation_safe cx (int_calls_exprs args) /\
  (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
            occurs_abi_decode_target target tops) ==>
  !e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  `~supported_expr_exists (const_name_root cx) e` by
    (fs[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  drule_all_then assume_tac expr_sim_inv_no_unallocated_bare_globals >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env st` by fs[expr_sim_inv_split_def] >>
  `~supported_exprs_exists (const_name_root_mods [(NONE,tops)]) args` by
    metis_tac[const_name_root_mods_singleton] >>
  `expr_body_pre_mods [(NONE,tops)] cenv cx env e st` by
    (mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`]
      body_log_snapshot_expr_pre_mods) >>
     simp[main_module_def, ALOOKUP_def]) >>
  drule_then assume_tac contract_inv_type_env >>
  drule_then assume_tac contract_inv_module_codes >>
  fs[expr_body_pre_split_def, expr_body_pre_mods_def, type_env_all_modules_def,
     type_env_def, FUNION_FEMPTY_2, EVERY_MEM, pairTheory.FORALL_PROD,
     supported_exprs_exists_every, EXISTS_MEM, source_body_call_supported_def] >>
  rpt strip_tac >> res_tac >> gvs[ALOOKUP_def]
QED

(* Body safety and root allocation checks give each argument expr_body_pre;
   expression evaluation then preserves the invariant and types its value. *)
Theorem body_log_args_ready:
  !tops ctx func cenv cx env args.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args /\
    body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
    supported_effect_free_exprs tops args /\ well_typed_exprs env args /\
    ~supported_exprs_exists (const_name_root cx) args /\
    ~supported_exprs_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) args /\
    alloc_limits_exprs cenv args /\
    call_evaluation_safe cx (int_calls_exprs args) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
              occurs_abi_decode_target target tops) ==>
    log_args_ready ctx func cenv cx (\es. expr_sim_inv cenv cx env es) args
Proof
  Induct_on `args` >> simp[log_args_ready_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `supported_effect_free_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_effect_free_expr_def]) >>
  qpat_x_assum `~supported_exprs_exists (const_name_root _) _`
    (strip_assume_tac o SIMP_RULE std_ss [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `well_typed_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once well_typed_expr_def]) >>
  qpat_x_assum `~supported_exprs_exists (\e. ~is_extcode e /\ _) (h::args)`
    (strip_assume_tac o SIMP_RULE std_ss [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `alloc_limits_exprs _ (h::args)`
    (strip_assume_tac o SIMP_RULE std_ss [Once alloc_limits_expr_def]) >>
  qpat_x_assum `call_evaluation_safe _ _` (assume_tac o
    SIMP_RULE std_ss [Once int_calls_expr_def]) >>
  qpat_x_assum `!target. supported_exprs_exists _ _ ==> _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_expr_exists_def, DISJ_IMP_THM,
                      FORALL_AND_THM]) >>
  gvs[body_exprs_ok_def] >>
  `call_evaluation_safe cx (int_calls_exprs args)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr h` >> simp[]) >>
  reverse conj_tac >- (strip_tac >> first_x_assum irule >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env h es` by
    (irule log_arg_body_pre >> simp[DE_MORGAN_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[body_expr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def, value_runtime_typed_def] >>
  `env.type_defs = get_tenv cx` suffices_by metis_tac[] >>
  gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]
QED

(* Supported pure expressions make no calls and pop nothing, so none can
   mutate memory or storage. *)
Theorem supported_effect_free_expr_no_mutate:
  (!tops e. supported_effect_free_expr tops e ==> ~expr_can_mutate cenv e) /\
  (!tops es. supported_effect_free_exprs tops es ==> ~exprs_can_mutate cenv es) /\
  (!tops fs. supported_effect_free_fields tops fs ==> ~named_exprs_can_mutate cenv fs) /\
  (!tops e. supported_effect_free_place_expr tops e ==> ~expr_can_mutate cenv e)
Proof
  ho_match_mp_tac supported_effect_free_expr_ind >>
  rw[supported_effect_free_expr_def, expr_can_mutate_def] >>
  gvs[supported_effect_free_expr_def, expr_can_mutate_def]
QED

Theorem supported_effect_free_exprs_bytestring_iff:
  !es. supported_effect_free_exprs tops es /\ well_typed_exprs env es ==>
    EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
               is_bytestring_type (expr_type e)) es
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once supported_effect_free_expr_def, Once well_typed_expr_def] >> strip_tac >>
  irule lowered_value_type_bytestring_iff >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[supported_effect_free_expr_def]) >>
  qexists_tac `env` >> simp[]
QED

Theorem body_log_assignable_abi_plan_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  (!k a. FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE) /\
  assignable_type (get_tenv cx) ty ==>
  abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)
Proof
  strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_mods_def] >>
  irule type_to_abi_enc_info_plan >> simp[] >>
  qexists_tac `get_tenv cx` >> simp[] >>
  rpt strip_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >> gvs[expr_sim_inv_mods_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem body_log_assignable_abi_plan:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  assignable_type (get_tenv cx) ty ==>
  abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)
Proof
  simp[expr_sim_inv_split_def] >> metis_tac[body_log_runtime_struct_namespace,
    body_log_assignable_abi_plan_mods]
QED

Theorem body_log_event_tuple_abi_plan_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  (!k a. FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE) /\
  tys <> [] /\
  EVERY (supported_nested_type supported_event_leaf_type (LENGTH (main_module mods)) (main_module mods)) tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv ==>
  abi_enc_plan (get_tenv cx) (TupleT tys)
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys))
Proof
  strip_tac >>
  `assignable_type (get_tenv cx) (TupleT tys)` suffices_by
    metis_tac[body_log_assignable_abi_plan_mods] >>
  drule_then assume_tac contract_inv_main_module >>
  `type_env (main_module mods) SUBMAP get_tenv cx` by
    metis_tac[body_main_type_env_submap, contract_inv_module_codes] >>
  qspecl_then [`supported_event_leaf_type`, `LENGTH (main_module mods)`, `main_module mods`, `TupleT tys`]
    mp_tac supported_nested_evaluated_assignable >> simp[] >>
  disch_then (qspecl_then [`get_tenv cx`, `{}`, `tv`] mp_tac) >>
  simp[DRESTRICT_UNIV, Once supported_nested_type_def, NULL_EQ]
QED

Theorem body_log_actual_tuple_abi_plan_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  (!k a. FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE) /\
  tys <> [] /\ EVERY (supported_place_type (main_module mods)) tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv ==>
  abi_enc_plan (get_tenv cx) (TupleT tys)
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys))
Proof
  strip_tac >>
  `assignable_type (get_tenv cx) (TupleT tys)` suffices_by
    metis_tac[body_log_assignable_abi_plan_mods] >>
  drule_then assume_tac contract_inv_main_module >>
  `type_env (main_module mods) SUBMAP get_tenv cx` by
    metis_tac[body_main_type_env_submap, contract_inv_module_codes] >>
  `well_formed_type (get_tenv cx) (TupleT tys)` by
    simp[well_formed_type_def] >>
  simp[assignable_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def,
      vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  `EVERY IS_SOME (MAP (evaluate_type (get_tenv cx)) tys)` by
    (simp[GSYM IS_SOME_OPT_MMAP] >>
     Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) tys` >> gvs[]) >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[supported_place_evaluated_assignable]
QED

Theorem log_compatible_evaluated_widening:
  !dty lty tenv ltv dtv.
    event_arg_compatible dty lty /\
    evaluate_type tenv lty = SOME ltv /\
    evaluate_type tenv dty = SOME dtv ==>
    type_widens_to tenv lty dty
Proof
  simp[event_arg_compatible_alias_def, type_widens_to_def,
       well_formed_type_def]
QED

Theorem log_compatible_aggregate_source:
  !dty lty.
    event_arg_compatible dty lty /\
    ~is_word_type dty /\ ~is_bytestring_type dty ==>
    ~is_word_type lty /\ ~is_bytestring_type lty
Proof
  simp[event_arg_compatible_alias_def] >>
  metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type,
            valueCopyBytesTheory.arg_type_fits_bytestring_target]
QED

Theorem log_compatible_declared_value:
  !dty lty tenv ltv dtv v.
    event_arg_compatible dty lty /\
    evaluate_type tenv lty = SOME ltv /\
    evaluate_type tenv dty = SOME dtv /\ value_has_type ltv v ==>
    value_has_type dtv v /\ val_wf dtv v
Proof
  rpt strip_tac >>
  `type_widens_to tenv lty dty` by
    metis_tac[log_compatible_evaluated_widening] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
  strip_tac >> gvs[] >>
  metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]
QED

Theorem log_compatible_bounded_evaluation:
  (!lty dty cenv cx env es ltv.
    expr_sim_inv cenv cx env es /\ arg_type_fits lty dty /\
    evaluate_type (get_tenv cx) lty = SOME ltv /\
    type_memory_bytes cenv dty < 2 ** 64 ==>
    IS_SOME (evaluate_type (get_tenv cx) dty)) /\
  (!ltys dtys cenv cx env es ltvs.
    expr_sim_inv cenv cx env es /\ arg_types_fit ltys dtys /\
    OPT_MMAP (evaluate_type (get_tenv cx)) ltys = SOME ltvs /\
    SUM (MAP (type_memory_bytes cenv) dtys) < 2 ** 64 ==>
    IS_SOME (OPT_MMAP (evaluate_type (get_tenv cx)) dtys))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, evaluate_type_def, type_memory_bytes_def,
     AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  gvs[type_slot_size_def, vfmConstantsTheory.word_size_def,
      wordsTheory.dimword_def, evaluate_type_def, evaluate_types_OPT_MMAP, ETA_THM] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  CONV_TAC (DEPTH_CONV ETA_CONV)
  >~ [`m < 115792089237316195423570985008687907853269984665640564039457584007913129639936`]
  >- (qspec_then `m` mp_tac le_word_size_mul >>
      simp[vfmConstantsTheory.word_size_def] >> decide_tac)
  >~ [`m < 115792089237316195423570985008687907853269984665640564039457584007913129639936`]
  >- (qspec_then `m` mp_tac le_word_size_mul >>
      simp[vfmConstantsTheory.word_size_def] >> decide_tac)
  >~ [`ArrayTV _ (Dynamic m)`]
  >- (`0 < m` by decide_tac >>
      `type_memory_bytes cenv dty <= m * type_memory_bytes cenv dty` by
        (Cases_on `m` >> gvs[MULT_CLAUSES]) >>
      `type_memory_bytes cenv dty < 18446744073709551616` by decide_tac >>
      `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
        (first_x_assum (qspecl_then [`cenv`, `cx`, `env`, `es`, `tv`] mp_tac) >>
         simp[optionTheory.IS_SOME_EXISTS]) >>
      `0 < type_slot_size dtv` by
        metis_tac[cj 1 arg_type_fits_zero_slots, NOT_ZERO_LT_ZERO] >>
      `type_memory_bytes cenv dty = 32 * type_slot_size dtv` by
        metis_tac[expr_sim_inv_memory_size, cj 1 type_memory_size_slots] >>
      `32 * (m * type_slot_size dtv) + 32 < 18446744073709551616` by
        (qpat_x_assum `m * type_memory_bytes cenv dty + 32 < _` mp_tac >>
         qpat_assum `type_memory_bytes cenv dty = _`
           (fn th => simp_tac std_ss
             [th, MULT_ASSOC, Q.SPECL [`m`, `32`] MULT_COMM])) >>
      simp[] >> decide_tac)
  >~ [`ArrayTV _ (Fixed m)`]
  >- (`type_memory_bytes cenv dty <= m * type_memory_bytes cenv dty` by
        (Cases_on `m` >> gvs[MULT_CLAUSES]) >>
      `type_memory_bytes cenv dty < 18446744073709551616` by decide_tac >>
      `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
        (first_x_assum (qspecl_then [`cenv`, `cx`, `env`, `es`, `tv`] mp_tac) >>
         simp[optionTheory.IS_SOME_EXISTS]) >>
      `0 < type_slot_size dtv` by
        metis_tac[cj 1 arg_type_fits_zero_slots, NOT_ZERO_LT_ZERO] >>
      `type_memory_bytes cenv dty = 32 * type_slot_size dtv` by
        metis_tac[expr_sim_inv_memory_size, cj 1 type_memory_size_slots] >>
      `32 * (m * type_slot_size dtv) < 18446744073709551616` by
        (qpat_x_assum `m * type_memory_bytes cenv dty < _` mp_tac >>
         qpat_assum `type_memory_bytes cenv dty = _`
           (fn th => simp_tac std_ss
             [th, MULT_ASSOC, Q.SPECL [`m`, `32`] MULT_COMM])) >>
      simp[] >> decide_tac)
  >~ [`TupleTV _`]
  >- (`?dtvs. OPT_MMAP (evaluate_type (get_tenv cx)) dtys = SOME dtvs` by
        (first_x_assum (qspecl_then [`cenv`, `cx`, `env`, `es`, `tvs`] mp_tac) >>
         simp[optionTheory.IS_SOME_EXISTS]) >>
      `SUM (MAP (type_memory_bytes cenv) dtys) = type_memory_size_list dtvs` by
        (irule tuple_memory_bytes_size >> qexists_tac `get_tenv cx` >>
         simp[] >> metis_tac[expr_sim_inv_memory_size]) >>
      `type_slot_size_list dtvs <=
         115792089237316195423570985008687907853269984665640564039457584007913129639936` by
        (gvs[cj 2 type_memory_size_slots] >> decide_tac) >>
      simp[]) >>
  `type_memory_bytes cenv dty < 18446744073709551616 /\
   SUM (MAP (type_memory_bytes cenv) dtys) < 18446744073709551616` by
    decide_tac >>
  `IS_SOME (evaluate_type (get_tenv cx) dty) /\
   IS_SOME (OPT_MMAP (evaluate_type (get_tenv cx)) dtys)` by
    (conj_tac >> metis_tac[]) >>
  Cases_on `evaluate_type (get_tenv cx) dty` >>
  Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) dtys` >> gvs[]

QED
