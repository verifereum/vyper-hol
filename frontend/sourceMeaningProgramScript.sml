Theory sourceMeaningProgram
Ancestors
  sourceMeaningProgramDefs sourceMeaningStmt sourceMeaningStmtDefs sourceMeaningConst
  sourceMeaningRuntime sourceMeaningEnv sourceMeaningDefs sourceModuleCompile sourceModuleElaborate sourceModuleDecl
  sourceModuleContext sourceModuleSignature sourceModuleStmt sourceModuleEnv sourceModuleDefs sourceResolveModules sourceResolve
  sourceConstEnvProps sourceConstEnv sourceSyntax vyperInterpreter vyperState
  vyperContext vyperAST vyperTypeContract compileVyper alist list pair

Theorem source_meaning_collect_member:
  !xs ys. source_module_collect (MAP f xs) = SM_Ok ys ==>
  !x. MEM x xs ==> ?y. f x = SM_Ok y /\ MEM y ys
Proof
  Induct >> simp[source_module_collect_def, source_meaning_bind_success] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem source_meaning_resolve_collect_member:
  !xs ys. source_resolve_collect (MAP f xs) = SOME ys ==>
  !x. MEM x xs ==> ?y. f x = SOME y /\ MEM y ys
Proof
  Induct >> simp[source_resolve_collect_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem source_meaning_original_initializer:
  source_resolve_registry_declarations registry = SOME declarations /\
  MEM (owner,syntax) registry /\
  MEM (path,original) (source_resolve_initializers owner syntax) ==>
  ?resolved.
    source_resolve_candidate
      [source_resolve_module_scope owner syntax; source_resolve_prelude_scope]
      (source_resolve_table registry) original = SOME resolved /\
    MEM (path,resolved) declarations
Proof
  simp[source_resolve_registry_declarations_def, AllCaseEqs()] >> strip_tac >>
  drule_all source_meaning_resolve_collect_member >> strip_tac >>
  gvs[source_resolve_declarations_def] >>
  drule_all source_meaning_resolve_collect_member >> strip_tac >>
  gvs[AllCaseEqs()] >> simp[MEM_FLAT] >> metis_tac[]
QED

Theorem source_meaning_program_constants_transport:
  source_resolve_registry_constants registry = SOME (SCEnv_Resolved constants) ==>
  source_meaning_constants registry constants
Proof
  simp[source_resolve_registry_constants_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `SCEnv_Resolved _ = _` (assume_tac o SYM) >>
  simp[source_meaning_constants_def] >> conj_tac
  >- (drule source_meaning_resolve_derivation >> metis_tac[]) >>
  rpt strip_tac >>
  drule_all source_meaning_original_initializer >> strip_tac >>
  drule source_meaning_initializer_transport >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

(* Named source defaults/initializers keep their meaning under fresh finite
   dependency extension. Resolution identities stay fixed, and readiness names
   exactly the already-bound dependencies; new declarations cannot shadow them. *)
Theorem source_meaning_staged_extension:
  source_meaning_declarations seed declarations constants /\
  source_resolve_candidate scopes table original = SOME resolved /\
  source_const_ready seed resolved ==>
  !result. source_meaning_stage scopes table seed original result <=>
    source_meaning_stage scopes table constants original result
Proof
  strip_tac >> drule_all source_meaning_declarations_evaluation >> strip_tac >>
  simp[source_meaning_stage_def]
QED

(* Function body transport includes context creation and looks at the original
   declaration. It is not an equality of elaboration outputs used as semantics. *)
Theorem source_meaning_function_transport:
  source_meaning_bodies types (source_module_function_context ctx name args params)
    ret original_body ms next_types next /\
  source_module_args ctx args = SM_Ok params /\
  source_module_return_type ctx annotation = SM_Ok ret /\
  source_meaning_locals types (source_module_function_context ctx name args params) /\
  get_tenv cx = (source_module_function_context ctx name args params).sm_env.type_defs /\
  source_module_body fuel ctx slots
    (SD_Function name decorators args defaults annotation original_body) = SM_Ok tops /\
  ~MEM (SX_Name "abstract") decorators ==>
  ?vis mut nr raw ds ss.
    tops = [FunctionDecl vis mut nr raw name params ds ret ss] /\
    eval_stmts cx ss = source_meaning_execute cx ms
Proof
  simp[source_module_body_def, source_module_signature_def,
    source_meaning_bind_success, source_meaning_bind_pair_success, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (CONJUNCT2 source_meaning_body_transport) >> strip_tac >>
  simp[source_meaning_execute_def]
QED

Theorem source_meaning_bodies_member:
  source_module_bodies fuel ctx slots syntax = SM_Ok tops /\
  MEM declaration (source_module_declarations syntax) ==>
  ?emitted. source_module_body fuel ctx slots declaration = SM_Ok emitted /\
    (!tl. MEM tl emitted ==> MEM tl tops)
Proof
  simp[source_module_bodies_def, source_meaning_bind_success] >> strip_tac >> gvs[] >>
  drule_all source_meaning_collect_member >> strip_tac >>
  qexists_tac `y` >> simp[MEM_FLAT] >> metis_tac[]
QED

(* The actual context and code set used by module elaboration are exposed,
   rather than silently reusing pre-rewrite get_module_code equalities. *)
Theorem source_meaning_elaborate_member:
  source_module_elaborate_simple fuel trust keys program = SM_Ok retained ==>
  ?registry constants links signatures.
    source_resolve_program_registry program keys = SOME registry /\
    source_meaning_constants registry constants /\
    source_module_signature_modules fuel trust registry constants = SM_Ok signatures /\
    !owner syntax. MEM (owner,syntax) registry ==>
    ?bindings src tops.
      source_module_override_bindings trust links
        (source_module_signature_context trust registry constants signatures owner syntax).sm_bindings =
          SOME bindings /\
      source_module_bodies fuel
        ((source_module_signature_context trust registry constants signatures owner syntax)
          with sm_bindings := bindings) trust.smt_slots syntax = SM_Ok tops /\
      MEM (src,tops) (retained_executable retained)
Proof
  simp[source_module_elaborate_simple_def, source_meaning_bind_success,
    pairTheory.EXISTS_PROD] >> strip_tac >>
  drule source_module_link_program_simple_equations >> strip_tac >>
  drule source_meaning_program_constants_transport >> strip_tac >>
  gvs[source_module_elaborate_registry_def, source_meaning_bind_success, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `source_module_signature_modules _ _ module_registry constant_env = SM_Ok sigs` >>
  qmatch_asmsub_rename_tac `source_module_overrides _ _ _ = SOME overrides` >>
  qexistsl_tac [`constant_env`,`overrides`,`sigs`] >>
  simp[retained_executable_def] >> rpt strip_tac >>
  drule_all source_meaning_collect_member >> strip_tac >>
  gvs[source_meaning_bind_success, AllCaseEqs()] >> metis_tac[]
QED

(* Composition with the unchanged lower-trust compiler API. The conclusion
   retains genuine checking/compilation artifacts AND execution transport for
   the selected original entry. This is body-entry simulation, not bytecode
   simulation: existing backend correctness still has its own hypotheses. *)
Theorem source_meaning_compile_entry:
  source_module_compile fuel trust keys program layouts address finalizer policy =
    SM_Ok (retained,art,bytes) ==>
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art /\
  (?tops. retained_executable retained = [(NONE,tops)] /\
    compile_vyper finalizer policy tops = SOME bytes) /\
  ?registry constants signatures.
    source_resolve_program_registry program keys = SOME registry /\
    source_meaning_constants registry constants /\
    !owner syntax declaration.
      MEM (owner,syntax) registry /\
      MEM declaration (source_module_declarations syntax) ==>
      ?bindings src tops emitted.
        let ctx = (source_module_signature_context trust registry constants signatures owner syntax)
          with sm_bindings := bindings in
        source_module_body fuel ctx trust.smt_slots declaration = SM_Ok emitted /\
        MEM (src,tops) (retained_executable retained) /\
        (!tl. MEM tl emitted ==> MEM tl tops) /\
        (!types ret ms cx.
          source_meaning_entry program keys registry owner syntax declaration ctx types ret ms /\
          ~MEM (SX_Name "abstract") (case declaration of
            SD_Function n ds a d r b => ds | _ => []) /\
          source_meaning_locals types (case declaration of
            SD_Function n ds a d r b => case source_module_args ctx a of
              SM_Ok params => source_module_function_context ctx n a params | _ => ctx
            | _ => ctx) /\
          get_tenv cx = (case declaration of
            SD_Function n ds a d r b => case source_module_args ctx a of
              SM_Ok params => source_module_function_context ctx n a params | _ => ctx
            | _ => ctx).sm_env.type_defs ==>
          ?vis mut nr raw name params defaults ss.
            emitted = [FunctionDecl vis mut nr raw name params defaults ret ss] /\
            eval_stmts cx ss = source_meaning_execute cx ms)
Proof
  strip_tac >> drule source_module_compile_equations >> strip_tac >> simp[] >>
  drule source_meaning_elaborate_member >> strip_tac >>
  qexistsl_tac [`registry`,`constants`,`signatures`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all source_meaning_bodies_member >> strip_tac >>
  qexistsl_tac [`bindings`,`emitted`] >> simp[] >>
  rpt gen_tac >> simp[source_meaning_entry_def] >> rpt strip_tac >> gvs[] >>
  drule_all source_meaning_function_transport >> strip_tac >> metis_tac[]
QED
