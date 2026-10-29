Theory sourceMeaningCallTest
Ancestors
  sourceMeaningCallExampleDefs sourceMeaningCompile sourceMeaningDispatch sourceMeaningDecl
  sourceMeaningCall sourceMeaningCallDefs sourceMeaningProgram sourceMeaningProgramDefs
  sourceMeaningStmt sourceMeaningStmtDefs sourceMeaningDefs sourceMeaningConst sourceMeaningRuntime
  sourceModuleElaborate sourceModuleEnv sourceModuleDecl sourceModuleDefs sourceSyntax
  sourceResolveModules sourceResolve sourceExprDefs sourceTypeDefs sourceConstAST sourceConstAnnotation
  sourceConstEval sourceConstValue sourceConstEnv vyperInterpreter vyperState vyperContext
  vyperAST vyperValue finite_map alist list
Libs
  intLib wordsLib

Theorem source_meaning_call_original_constants:
  source_resolve_program_registry (SourceProgram source_meaning_call_syntax []) [["main"]] =
    SOME source_meaning_call_registry /\
  source_resolve_registry_constants source_meaning_call_registry =
    SOME (SCEnv_Resolved source_meaning_call_constants)
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_constant:
  !types scopes table constants original.
  source_meaning_stage scopes table constants original (SC_Value (SCV_Int 3)) ==>
  source_meaning_source types scopes table constants source_meaning_call_uint original
    (SM_Literal source_meaning_call_uint (IntL 3))
Proof
  rpt strip_tac >> irule sourceMeaningDefsTheory.constant >>
  qexists_tac `SCV_Int 3` >> simp[source_const_value_literal_def]
QED

Theorem source_meaning_call_ctx_fields:
  source_meaning_call_ctx.sm_scopes = source_module_scopes ["main"] source_meaning_call_syntax /\
  source_meaning_call_ctx.sm_table = source_resolve_table source_meaning_call_registry ++
    source_module_extra_prelude /\
  source_meaning_call_ctx.sm_constants = source_meaning_call_constants /\
  source_meaning_call_ctx.sm_owner = ["main"]
Proof
  simp[source_meaning_call_ctx_def, source_module_body_context_def, source_module_context_def]
QED

Theorem source_meaning_call_fctx_fields:
  source_meaning_call_fctx.sm_scopes =
    [("x",["main";"f";"x"])]::source_meaning_call_ctx.sm_scopes /\
  source_meaning_call_fctx.sm_table =
    (["main";"f";"x"],SR_Dynamic)::source_meaning_call_ctx.sm_table /\
  source_meaning_call_fctx.sm_constants = source_meaning_call_constants
Proof
  Cases_on `source_module_interface_fields source_meaning_call_ctx source_meaning_call_annotation` >>
  simp[source_meaning_call_fctx_def, source_module_function_context_def,
    source_module_annotated_local_def, source_module_local_def,
    source_meaning_call_ctx_fields]
QED

Theorem source_meaning_call_body_source:
  source_meaning_bodies source_meaning_call_types source_meaning_call_fctx
    source_meaning_call_uint
    [SS_Return (SOME (SX_Binary SCB_Add (SX_Name "x") (SX_Name "N")))]
    source_meaning_call_body source_meaning_call_types source_meaning_call_fctx
Proof
  simp[source_meaning_call_body_def] >> irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_meaning_call_fctx`,`source_meaning_call_types`] >>
  conj_tac >- irule sourceMeaningStmtDefsTheory.empty >>
  irule sourceMeaningStmtDefsTheory.return_value >> irule sourceMeaningDefsTheory.binary >>
  simp[] >> rpt conj_tac
  >- (EVAL_TAC >> simp[] >> EVAL_TAC)
  >- (simp[source_meaning_stage_def, GSYM source_meaning_const_correct] >>
      EVAL_TAC >> simp[] >> EVAL_TAC)
  >- (irule sourceMeaningDefsTheory.name >>
      simp[source_expr_path_def, source_meaning_stage_def, GSYM source_meaning_const_correct,
        source_meaning_call_fctx_fields, source_meaning_call_ctx_fields] >>
      rpt conj_tac >> EVAL_TAC >> simp[] >> EVAL_TAC) >>
  irule source_meaning_call_constant >>
  simp[source_meaning_stage_def, GSYM source_meaning_const_correct] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_call_source:
  source_meaning_module source_meaning_call_ctx source_meaning_call_syntax
    source_meaning_call_denotation
Proof
  simp[source_meaning_module_def, source_meaning_call_syntax_def,
    source_meaning_call_denotation_def, source_module_declarations_def] >> conj_tac
  >- (irule sourceMeaningCallDefsTheory.constant >> conj_tac
      >- (qexists_tac `SourceTypeResolution (Type source_meaning_call_uint) [SCQ_Constant] []` >>
          EVAL_TAC) >>
      irule source_meaning_call_constant >>
      simp[source_meaning_stage_def, GSYM source_meaning_const_correct] >>
      EVAL_TAC >> simp[] >> EVAL_TAC) >>
  simp[source_meaning_call_function_def] >>
  irule (SIMP_RULE (srw_ss()) [source_module_visibility_def,source_module_mutability_def]
    (Q.INST [`ds` |-> `["external";"pure"]`] (SPEC_ALL sourceMeaningCallDefsTheory.function))) >>
  simp[] >> rpt conj_tac
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- (simp[source_meaning_default_sources_def] >> irule source_meaning_call_constant >>
      simp[source_meaning_stage_def, GSYM source_meaning_const_correct] >>
      EVAL_TAC >> simp[] >> EVAL_TAC) >>
  qexistsl_tac [`source_meaning_call_fctx`,`source_meaning_call_types`] >>
  metis_tac[source_meaning_call_body_source, source_meaning_call_fctx_def,
    source_meaning_call_types_def]
QED

Theorem source_meaning_call_build:
  source_module_bodies 12 source_meaning_call_ctx [] source_meaning_call_syntax =
    SM_Ok source_meaning_call_tops
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_code:
  LIST_REL (source_meaning_decl_code FEMPTY)
    source_meaning_call_denotation source_meaning_call_tops
Proof
  assume_tac source_meaning_call_source >> assume_tac source_meaning_call_build >>
  drule_all source_meaning_module_transport >>
  `source_meaning_call_ctx.sm_env.type_defs = FEMPTY` by EVAL_TAC >> simp[]
QED

Theorem source_meaning_call_dispatch:
  !orc tx. ALOOKUP source_meaning_call_machine.exports tx.target = NONE /\
    tx.target = 0w ==>
  call_external orc source_meaning_call_machine tx =
    source_meaning_call orc source_meaning_call_machine tx source_meaning_call_denotation
Proof
  rpt strip_tac >> irule source_meaning_call_transport >> simp[] >>
  qexists_tac `source_meaning_call_tops` >>
  `type_env_all_modules [(NONE,source_meaning_call_tops)] = FEMPTY` by EVAL_TAC >>
  simp[source_meaning_call_code] >> EVAL_TAC
QED

Theorem source_meaning_call_default_return:
  FST (source_meaning_call NONE source_meaning_call_machine
    (empty_call_txn with function_name := "f") source_meaning_call_denotation) = INL (IntV 6)
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_argument_return:
  FST (source_meaning_call NONE source_meaning_call_machine
    (empty_call_txn with <| function_name := "f"; args := [IntV 7] |>)
      source_meaning_call_denotation) = INL (IntV 10)
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_excess_arguments:
  FST (source_meaning_call NONE source_meaning_call_machine
    (empty_call_txn with <| function_name := "f"; args := [IntV 7;IntV 8] |>)
      source_meaning_call_denotation) = INR (Error (RuntimeError "call args length"))
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_constructor:
  load_contract orc initial_machine_state
    (empty_call_txn with function_name := "__init__") [(NONE,source_meaning_call_tops)] [] =
  source_meaning_load orc initial_machine_state
    (empty_call_txn with function_name := "__init__") [(NONE,source_meaning_call_tops)] []
      source_meaning_call_denotation
Proof
  `type_env_all_modules [(NONE,source_meaning_call_tops)] = FEMPTY` by EVAL_TAC >>
  irule source_meaning_load_transport >> simp[source_meaning_call_code]
QED

Theorem source_meaning_call_installed_constant:
  source_meaning_globals FEMPTY source_meaning_call_denotation FEMPTY =
    SOME (FEMPTY |+ ("N",(BaseTV (UintT 256),IntV 3)))
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_runtime_return:
  FST (call_external NONE source_meaning_call_machine
    (empty_call_txn with function_name := "f")) = INL (IntV 6)
Proof
  `call_external NONE source_meaning_call_machine
      (empty_call_txn with function_name := "f") =
    source_meaning_call NONE source_meaning_call_machine
      (empty_call_txn with function_name := "f") source_meaning_call_denotation` by
    (irule source_meaning_call_dispatch >> EVAL_TAC) >>
  simp[source_meaning_call_default_return]
QED

Theorem source_meaning_call_default_constructor_store:
  ?am rqs imms.
    source_meaning_load NONE initial_machine_state
      (empty_call_txn with function_name := "__init__") [(NONE,source_meaning_call_tops)] []
        source_meaning_call_denotation = INL (am,rqs) /\
    ALOOKUP am.immutables 0w = SOME imms /\
    FLOOKUP (get_source_immutables NONE imms) "N" = SOME (BaseTV (UintT 256),IntV 3)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_call_explicit_constructor_source:
  source_meaning_declaration source_meaning_call_ctx source_meaning_call_ctor_source
    source_meaning_call_ctor_meaning
Proof
  simp[source_meaning_call_ctor_source_def, source_meaning_call_ctor_meaning_def] >>
  irule (SIMP_RULE (srw_ss()) [source_module_visibility_def,source_module_mutability_def]
    (Q.INST [`ds` |-> `["deploy";"payable"]`] (SPEC_ALL sourceMeaningCallDefsTheory.function))) >>
  simp[] >> rpt conj_tac
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- (simp[source_meaning_default_sources_def] >> irule source_meaning_call_constant >>
      simp[source_meaning_stage_def, GSYM source_meaning_const_correct] >>
      EVAL_TAC >> simp[] >> EVAL_TAC) >>
  qexistsl_tac [`source_module_function_context source_meaning_call_ctx "__init__"
      [SourceArg "x" (SOME source_meaning_call_annotation)] [("x",source_meaning_call_uint)]`,
    `source_meaning_parameter_types source_meaning_call_ctx "__init__"
      [SourceArg "x" (SOME source_meaning_call_annotation)] [("x",source_meaning_call_uint)]`] >>
  irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_module_function_context source_meaning_call_ctx "__init__"
      [SourceArg "x" (SOME source_meaning_call_annotation)] [("x",source_meaning_call_uint)]`,
    `source_meaning_parameter_types source_meaning_call_ctx "__init__"
      [SourceArg "x" (SOME source_meaning_call_annotation)] [("x",source_meaning_call_uint)]`] >>
  simp[source_meaning_body_rules]
QED

Theorem source_meaning_call_explicit_constructor_build:
  source_module_body 12 source_meaning_call_ctx [] source_meaning_call_ctor_source =
    SM_Ok [source_meaning_call_ctor_code]
Proof
  EVAL_TAC
QED

Theorem source_meaning_call_explicit_constructor_code:
  source_meaning_decl_code FEMPTY source_meaning_call_ctor_meaning source_meaning_call_ctor_code
Proof
  assume_tac source_meaning_call_explicit_constructor_source >>
  assume_tac source_meaning_call_explicit_constructor_build >>
  drule_all source_meaning_declaration_transport >>
  `source_meaning_call_ctx.sm_env.type_defs = FEMPTY` by EVAL_TAC >> simp[]
QED

Theorem source_meaning_call_explicit_constructor:
  load_contract orc am tx [(NONE,source_meaning_call_ctor_code::source_meaning_call_tops)] exps =
  source_meaning_load orc am tx [(NONE,source_meaning_call_ctor_code::source_meaning_call_tops)] exps
    (source_meaning_call_ctor_meaning::source_meaning_call_denotation)
Proof
  `type_env_all_modules [(NONE,source_meaning_call_ctor_code::source_meaning_call_tops)] = FEMPTY`
    by EVAL_TAC >>
  irule source_meaning_load_transport >>
  simp[source_meaning_call_code, source_meaning_call_explicit_constructor_code]
QED

fun audit_source_call thy =
  let fun check (name,th) = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in if null (hyp th) andalso null axioms andalso
      List.all (fn tag => tag = "DISK_THM") oracles then ()
      else raise Fail ("source call kernel audit: " ^ thy ^ "." ^ name) end
      val exports = DB.thms thy
  in List.app check exports; print ("SOURCE_CALL_KERNEL_CLOSED " ^ thy ^ " exports=" ^
    Int.toString (length exports) ^ "\n") end;
val () = List.app audit_source_call
  ["sourceMeaningEnv","sourceMeaningCallDefs","sourceMeaningCall","sourceMeaningDecl",
   "sourceMeaningDispatch","sourceMeaningCompile","sourceMeaningCallExampleDefs","sourceMeaningCallTest"];
