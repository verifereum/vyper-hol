(* Shared event metadata and pure argument readiness for the Log cases. *)
Theory bodySimLogArgs
Ancestors
  allocLimits allocLimitsProps
  bodyMemAssignTopCopyFacts bodyMemoryDefs stmtSimLogDataFrame
  exprSimMemDefs venomMemDefs
  exprSimSource bodyExprPreFacts exprSimHypsDefs list bodySim bodySimStmtCases stmtSimLog exprSimHyps
  compileEnv compileVyper supportedStmts supportedDecls supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperEvent vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness exprLowering retAbiPlanProps abiDecoderMembers finite_map pred_set

(* Namespace support and first-module lookup, including duplicate entries. *)
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

(* A lookup in the combined environment has a selected module, even when
   module entries are duplicated. Only namespace existence is needed here. *)
Theorem log_type_env_module_exists[local]:
  !mods src id a.
    FLOOKUP (type_env_all_modules mods) (src,id) = SOME a ==>
    ?ts. ALOOKUP mods src = SOME ts
Proof
  Induct >> simp[type_env_all_modules_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[type_env_all_modules_def, FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP (type_env_for_module h0 h1) (src,id)` >>
  simp[] >> rpt strip_tac
  >- (Cases_on `h0 = src` >> simp[] >> metis_tac[]) >>
  drule log_type_env_namespace >> strip_tac >> gvs[]
QED

Theorem body_log_runtime_struct_namespace:
  !tops ctx cenv cx k a.
    body_inv tops ctx cenv cx /\
    FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE
Proof
  rpt strip_tac >> PairCases_on `k` >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  gvs[get_tenv_def] >>
  drule log_type_env_module_exists >> strip_tac >>
  gvs[body_inv_def, get_module_code_def] >> metis_tac[]
QED

Theorem body_main_type_env_submap:
  !cx tops. get_module_code cx NONE = SOME tops ==>
    type_env tops SUBMAP get_tenv cx
Proof
  rw[get_module_code_def, get_tenv_def, type_env_def, AllCaseEqs()] >>
  simp[module_type_env_submap]
QED


Theorem supported_nested_evaluation_env[local]:
  !leaf fuel tops ty.
    leaf = supported_scalar_type ==>
    !large removed.
      supported_nested_type leaf fuel tops ty /\ type_env tops SUBMAP large ==>
      evaluate_type (DRESTRICT (type_env tops) (COMPL removed)) ty =
      evaluate_type (DRESTRICT large (COMPL removed)) ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `supported_scalar_type ty`
  >- (Cases_on `ty` >>
      gvs[supported_scalar_type_def, supported_word_type_def,
          supported_string_type_def, vyperValueTheory.evaluate_type_def]) >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  Cases_on `ty` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac
  >~ [`evaluate_type _ (TupleT tys)`]
  >- (`OPT_MMAP (evaluate_type (DRESTRICT (type_env tops) (COMPL removed))) tys =
       OPT_MMAP (evaluate_type (DRESTRICT large (COMPL removed))) tys` by
        (irule OPT_MMAP_cong >> gvs[EVERY_MEM] >> metis_tac[]) >>
      gvs[vyperValueTheory.evaluate_type_def,
          vyperValueTheory.evaluate_types_OPT_MMAP])
  >~ [`evaluate_type _ (ArrayT t b)`]
  >- (Cases_on `b` >> gvs[] >>
      `evaluate_type (DRESTRICT (type_env tops) (COMPL removed)) t =
       evaluate_type (DRESTRICT large (COMPL removed)) t` by metis_tac[] >>
      simp[vyperValueTheory.evaluate_type_def]) >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  rename1 `supported_struct_fields tops p = SOME fields` >>
  drule supported_struct_fields_type_env >> strip_tac >>
  `FLOOKUP large p = SOME (StructArgs fields)` by
    metis_tac[FLOOKUP_SUBMAP] >>
  Cases_on `p IN removed` >>
  simp[vyperValueTheory.evaluate_type_def, FLOOKUP_DRESTRICT] >>
  simp[DRESTRICT_DOMSUB, vyperValueTheory.evaluate_types_OPT_MMAP] >>
  `COMPL removed DELETE p = COMPL (p INSERT removed)` by
    (simp[EXTENSION] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `OPT_MMAP (evaluate_type (DRESTRICT (type_env tops) (COMPL (p INSERT removed))))
       (MAP SND fields) =
   OPT_MMAP (evaluate_type (DRESTRICT large (COMPL (p INSERT removed))))
       (MAP SND fields)` by
    (irule OPT_MMAP_cong >>
     gvs[EVERY_MEM, combinTheory.o_DEF, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  simp[]
QED

Theorem supported_nested_abi_env[local]:
  !leaf fuel tops ty.
    leaf = supported_scalar_type ==>
    !large removed.
      supported_nested_type leaf fuel tops ty /\ type_env tops SUBMAP large ==>
      vyper_to_abi_type (DRESTRICT (type_env tops) (COMPL removed)) ty =
      vyper_to_abi_type (DRESTRICT large (COMPL removed)) ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `supported_scalar_type ty`
  >- (Cases_on `ty` >>
      gvs[supported_scalar_type_def, supported_word_type_def,
          supported_string_type_def]) >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  Cases_on `ty` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac
  >~ [`FLOOKUP _ p`]
  >- (Cases_on `supported_struct_fields tops p` >> gvs[] >>
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

Theorem supported_nested_evaluated_assignable[local]:
  !leaf fuel tops ty.
    leaf = supported_scalar_type ==>
    !large removed tv.
      supported_nested_type leaf fuel tops ty /\ type_env tops SUBMAP large /\
      evaluate_type (DRESTRICT large (COMPL removed)) ty = SOME tv ==>
      assignable_type (DRESTRICT large (COMPL removed)) ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `supported_scalar_type ty`
  >- (irule supported_scalar_type_assignable >>
      simp[well_formed_type_def]) >>
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
    evaluate_type tenv ty = SOME tv ==>
    assignable_type tenv ty
Proof
  rpt strip_tac >>
  qspecl_then [`supported_scalar_type`, `LENGTH tops`, `tops`, `ty`]
    mp_tac supported_nested_evaluated_assignable >> simp[] >>
  disch_then (qspecl_then [`tenv`, `{}`, `tv`] mp_tac) >>
  gvs[supported_place_type_def, DRESTRICT_UNIV]
QED

Theorem supported_place_abi_env:
  !tops cx ty.
    get_module_code cx NONE = SOME tops /\ supported_place_type tops ty ==>
    vyper_to_abi_type (type_env tops) ty = vyper_to_abi_type (get_tenv cx) ty
Proof
  rpt strip_tac >> drule body_main_type_env_submap >> strip_tac >>
  qspecl_then [`supported_scalar_type`, `LENGTH tops`, `tops`, `ty`]
    mp_tac supported_nested_abi_env >>
  simp[supported_place_type_def] >>
  disch_then (qspecl_then [`get_tenv cx`, `{}`] mp_tac) >>
  gvs[supported_place_type_def, DRESTRICT_UNIV]
QED

Theorem supported_place_abi_types_env[local]:
  !tys tops cx.
    get_module_code cx NONE = SOME tops /\ EVERY (supported_place_type tops) tys ==>
    vyper_to_abi_types (type_env tops) tys = vyper_to_abi_types (get_tenv cx) tys
Proof
  Induct >> simp[] >> metis_tac[supported_place_abi_env]
QED

(* ===== The event's metadata ===== *)

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

(* A scalar type's ABI type does not look at the type environment. *)
Theorem scalar_abi_types_env[local]:
  !ts env env'.
    EVERY supported_scalar_type ts ==>
    vyper_to_abi_types env ts = vyper_to_abi_types env' ts
Proof
  Induct >> simp[] >> Cases >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED

(* body_inv's ce_event_info is build_event_info's for the program, whose
   event names supported_program makes distinct, and the source finds the
   same declaration in the module get_module_code gives. *)
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
  rpt gen_tac >> strip_tac >>
  drule supported_event_fields_some >> strip_tac >> gvs[] >>
  `EVERY supported_scalar_type (MAP (SND o FST) fields) /\
   LENGTH (FILTER I (MAP SND fields)) <= 3` by
    (gvs[body_inv_def, supported_program_def,
         supported_declaration_headers_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e tops ==> supported_declaration_header _ _`
       drule >>
     simp[supported_declaration_header_def, EVERY_MAP, combinTheory.o_DEF,
          MEM_MAP, PULL_EXISTS] >>
     strip_tac >> gvs[EVERY_MEM]) >>
  `event_decl_unique name tops` by
    gvs[body_inv_def, supported_program_def,
        supported_declaration_names_def, event_names_unique] >>
  gvs[body_inv_def, nsid_to_string_def, build_event_info_lookup_event_metadata_in,
      lookup_event_metadata_def, get_module_code_def, AllCaseEqs(),
      event_hash_def] >>
  metis_tac[scalar_abi_types_env]
QED

(* Aggregate fields share the same declaration and hash at the body site.
   This is metadata only: actual argument types need not equal field types. *)
Theorem body_log_aggregate_metadata:
  !tops ctx cenv cx id fields.
    body_inv tops ctx cenv cx /\ supported_event_fields tops id = SOME fields ==>
    ?h. cenv.ce_event_info (nsid_to_string id) =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        LENGTH (FILTER I (MAP SND fields)) <= 3 /\
        EVERY (\f. if SND f then supported_scalar_type (SND (FST f))
                    else supported_place_type tops (SND (FST f))) fields
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_event_fields_some >> strip_tac >> gvs[] >>
  `EVERY (\f. if SND f then supported_scalar_type (SND (FST f))
              else supported_place_type tops (SND (FST f))) fields /\
   LENGTH (FILTER I (MAP SND fields)) <= 3` by
    (gvs[body_inv_def, supported_program_def,
         supported_declaration_headers_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e tops ==> supported_declaration_header _ _` drule >>
     simp[supported_declaration_header_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
     metis_tac[]) >>
  `EVERY (supported_place_type tops) (MAP (SND o FST) fields)` by
    (gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, combinTheory.o_DEF] >>
     rpt strip_tac >>
     qpat_x_assum `!a b c. MEM ((a,b),c) fields ==> _` drule >>
     Cases_on `p_2'` >> simp[] >>
     simp[supported_place_type_def, Once supported_nested_type_def]) >>
  `vyper_to_abi_types (type_env tops) (MAP (SND o FST) fields) =
   vyper_to_abi_types (get_tenv cx) (MAP (SND o FST) fields)` by
    (irule supported_place_abi_types_env >> gvs[body_inv_def]) >>
  `event_decl_unique name tops` by
    gvs[body_inv_def, supported_program_def,
        supported_declaration_names_def, event_names_unique] >>
  gvs[body_inv_def, nsid_to_string_def, build_event_info_lookup_event_metadata_in,
      lookup_event_metadata_def, get_module_code_def, AllCaseEqs(), event_hash_def]
QED

(* ===== The arguments ===== *)

(* The argument's explicit body-safety facts supply the call preconditions. *)
Theorem log_arg_body_pre[local]:
  !tops ctx cenv cx env e calls es.
    body_stmt_safe tops (Expr e) /\ ~is_extcode e /\
    body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
    well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, listTheory.EVERY_CONJ, GSYM expr_has_evm_run_def]) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    fs[body_inv_def] >>
  `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es`, `calls`]
    irule stmt_expr_body_pre >> simp[] >> metis_tac[]
QED

(* Body safety and root allocation checks give each argument expr_body_pre;
   expression evaluation then preserves the invariant and types its value. *)
Theorem body_log_args_ready:
  !tops ctx func cenv cx env args.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args /\
    body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
    supported_pure_exprs tops args /\ well_typed_exprs env args /\
    ~supported_exprs_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
    call_evaluation_safe cx (int_calls_exprs args) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
              occurs_abi_decode_target target tops) ==>
    log_args_ready ctx func cenv cx (\es. expr_sim_inv cenv cx env es) args
Proof
  Induct_on `args` >> simp[log_args_ready_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `supported_pure_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_pure_expr_def]) >>
  qpat_x_assum `well_typed_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once well_typed_expr_def]) >>
  qpat_x_assum `~supported_exprs_exists _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
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
Theorem supported_pure_expr_no_mutate:
  (!tops e. supported_pure_expr tops e ==> ~expr_can_mutate cenv e) /\
  (!tops es. supported_pure_exprs tops es ==> ~exprs_can_mutate cenv es) /\
  (!tops fs. supported_pure_fields tops fs ==> ~named_exprs_can_mutate cenv fs) /\
  (!tops e. supported_place_expr tops e ==> ~expr_can_mutate cenv e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rw[supported_pure_expr_def, expr_can_mutate_def] >>
  gvs[supported_pure_expr_def, expr_can_mutate_def]
QED

Theorem supported_pure_exprs_bytestring_iff:
  !es. supported_pure_exprs tops es /\ well_typed_exprs env es ==>
    EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
               is_bytestring_type (expr_type e)) es
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once supported_pure_expr_def, Once well_typed_expr_def] >> strip_tac >>
  irule lowered_value_type_bytestring_iff >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[supported_pure_expr_def]) >>
  qexists_tac `env` >> simp[]
QED

(* The plan can be instantiated in the actual runtime environment itself;
   no reverse SUBMAP or global-environment equality is needed. *)
Theorem body_log_assignable_abi_plan:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  assignable_type (get_tenv cx) ty ==>
  abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)
Proof
  strip_tac >>
  `!k a. FLOOKUP (get_tenv cx) k = SOME (StructArgs a) ==> FST k = NONE` by
    metis_tac[body_log_runtime_struct_namespace] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_def] >>
  irule type_to_abi_enc_info_plan >> simp[] >>
  qexists_tac `get_tenv cx` >> simp[] >>
  metis_tac[expr_sim_inv_memory_size]
QED

(* Non-bytestring stores copy the full type capacity, including unused
   dynamic-array slots. The capture bound already accounts for that size. *)
Theorem body_log_capture_bulk_bound:
  expr_store_bound cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  eval_operand op s = SOME w ==>
  type_memory_size tv = 0 \/
  w2n w + type_memory_size tv <= s.vs_alloca_next
Proof
  strip_tac >>
  drule_all topcopy_val_store_size >> strip_tac >>
  gvs[expr_store_bound_def] >> metis_tac[]
QED

(* Both registered allocations and local regions end below the frontier.
   This also covers zero-footprint captures without a positivity premise. *)
Theorem body_log_capture_source_apart:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\
  s.vs_alloca_next <= b ==>
  log_source_apart cx b n (op,ty) v s
Proof
  strip_tac >> irule log_placement_source_apart >>
  qexistsl_tac [`ce`, `es`, `sa`, `sb`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> disj1_tac >>
      drule_all body_local_region_frontier >> decide_tac) >>
  rpt strip_tac >> disj1_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       alloca_inv_def, alloca_next_valid_def] >>
  strip_tac >>
  qpat_x_assum `!aid base sz. _` drule >> decide_tac
QED

(* Whole-tail readiness is retained in the capture invariant: successful
   evaluation supplies the witness needed to expose the next ready tail. *)
Theorem body_log_args_pure_step:
  log_args_ready ctx func cenv cx Inv (e::tail) /\
  supported_pure_exprs tops (e::tail) /\ Inv es ==>
  expr_sim ctx func cenv cx (expr_type e) e es /\
  post_value_type cenv e = expr_type e /\
  !v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) ==>
    (log_args_ready ctx func cenv cx Inv tail /\
     supported_pure_exprs tops tail /\ Inv es1) /\
    es1.scopes = es.scopes /\
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv v
Proof
  simp[log_args_ready_def, Once supported_pure_expr_def] >>
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[supported_pure_int_calls, post_value_type_no_calls] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `es1.scopes = es.scopes` by
    (irule bodySimAugPlaceLoadTheory.aug_place_rhs_scopes >>
     qexistsl_tac [`cx`, `e`, `INL v`, `tops`] >>
     simp[supported_expr_def]) >>
  `?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                      read_result cx tv s1 = (INL v,t1)` by
    (gvs[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem log_compatible_nested_support[local]:
  (!fty aty. event_arg_compatible fty aty ==>
    !fuel tops. supported_nested_type supported_scalar_type fuel tops fty ==>
                supported_nested_type supported_scalar_type fuel tops aty) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
    !fuel tops. EVERY (supported_nested_type supported_scalar_type fuel tops) fts ==>
                EVERY (supported_nested_type supported_scalar_type fuel tops) ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rpt strip_tac >>
  TRY (qpat_x_assum `supported_nested_type _ _ _ _` mp_tac) >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >>
  rpt strip_tac >>
  gvs[event_arg_compatible_def] >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >>
  metis_tac[listTheory.NULL_EQ, listTheory.LENGTH_NIL]
QED

(* Field support, unlike purity alone, constrains actual annotations. *)
Theorem log_compatible_place_support:
  supported_place_type tops fty /\ event_arg_compatible fty aty ==>
  supported_place_type tops aty
Proof
  metis_tac[log_compatible_nested_support, supported_place_type_def]
QED

Theorem log_compatible_args_support:
  !args (fields : ((string # type) # bool) list).
  EVERY (\((_,fty),_). supported_place_type tops fty) fields /\
  LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields ==>
  EVERY (supported_place_type tops o expr_type) args
Proof
  Induct >> Cases_on `fields` >> simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[] >> metis_tac[log_compatible_place_support]
QED

Theorem log_widened_fields_args_support:
  !args (fields : ((string # type) # bool) list).
  EVERY (\((_,fty),indexed). if indexed then supported_scalar_type fty
                              else supported_place_type tops fty) fields /\
  LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields ==>
  EVERY (supported_place_type tops o expr_type) args
Proof
  rpt strip_tac >> irule log_compatible_args_support >>
  qexists_tac `fields` >> simp[] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  match_mp_tac listTheory.EVERY_MONOTONIC >>
  Cases >> Cases_on `q` >> Cases_on `r` >> simp[] >>
  metis_tac[supported_place_type_def, supported_nested_type_def]
QED

(* Successful evaluation of the actual data tuple supplies memberwise
   well-formedness; support supplies assignability in the runtime map. *)
Theorem body_log_actual_tuple_abi_plan:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  tys <> [] /\ EVERY (supported_place_type tops) tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv ==>
  abi_enc_plan (get_tenv cx) (TupleT tys)
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys))
Proof
  strip_tac >> irule body_log_assignable_abi_plan >>
  reverse conj_tac >- metis_tac[] >>
  `type_env tops SUBMAP get_tenv cx` by
    (irule body_main_type_env_submap >> gvs[body_inv_def]) >>
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
