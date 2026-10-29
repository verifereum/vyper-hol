Theory sourceMeaningExportTest
Ancestors
  sourceMeaningAggregateTest sourceMeaningAggregateExample sourceMeaningModules
  sourceMeaningDecl sourceMeaningCall sourceMeaningCallDefs sourceMeaningProgramDefs
  sourceMeaningStmt sourceMeaningStmtDefs sourceMeaningRuntime sourceMeaningCode
  sourceMeaningDefs sourceMeaningValue sourceModuleDecl sourceModuleEnv sourceModuleDefs
  sourceSyntax sourceConstAnnotation sourceTypeDefs vyperInterpreter vyperState
  vyperContext vyperAST vyperValue vyperValueOperation finite_map alist list
Libs
  intLib wordsLib

Definition source_meaning_export_ctx_def:
  source_meaning_export_ctx = source_module_context source_meaning_aggregate_trust
    source_meaning_aggregate_registry source_meaning_aggregate_constants ["lib"]
    (EL 2 (MAP SND source_meaning_aggregate_registry))
End
Definition source_meaning_export_decl_def:
  source_meaning_export_decl = SD_Function "read" [SX_Name "external";SX_Name "pure"]
    [] [] (SOME (SCA_Name ["uint256"])) [SS_Return (SOME (SX_Name "A"))]
End
Definition source_meaning_export_meaning_def:
  source_meaning_export_meaning = SDM_Function External Pure F F "read" [] []
    (BaseT (UintT 256)) [SBM_Return (SOME (SM_Literal (BaseT (UintT 256)) (IntL 6)))]
End
Definition source_meaning_export_code_def:
  source_meaning_export_code = FunctionDecl External Pure F F "read" [] []
    (BaseT (UintT 256)) [Return (SOME (Literal (BaseT (UintT 256)) (IntL 6)))]
End

Definition source_meaning_export_fctx_def:
  source_meaning_export_fctx =
    source_module_function_context source_meaning_export_ctx "read" [] []
End

Theorem source_meaning_export_body_source:
  source_meaning_bodies [] source_meaning_export_fctx (BaseT (UintT 256))
    [SS_Return (SOME (SX_Name "A"))]
    [SBM_Return (SOME (SM_Literal (BaseT (UintT 256)) (IntL 6)))]
    [] source_meaning_export_fctx
Proof
  irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_meaning_export_fctx`,`[]`] >>
  simp[sourceMeaningStmtDefsTheory.empty] >>
  irule sourceMeaningStmtDefsTheory.return_value >>
  irule sourceMeaningDefsTheory.constant >> qexists_tac `SCV_Int 6` >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_export_source:
  source_meaning_declaration source_meaning_export_ctx source_meaning_export_decl
    source_meaning_export_meaning
Proof
  simp[source_meaning_export_decl_def, source_meaning_export_meaning_def] >>
  simp[Once source_meaning_declaration_cases] >>
  qexistsl_tac [`["external";"pure"]`,`source_meaning_export_fctx`,`[]`] >>
  simp[source_meaning_parameter_types_def, GSYM source_meaning_export_fctx_def,
    source_meaning_export_body_source] >> EVAL_TAC
QED

Theorem source_meaning_export_build:
  source_module_body 12 source_meaning_export_ctx [] source_meaning_export_decl =
    SM_Ok [source_meaning_export_code]
Proof
  EVAL_TAC
QED

Theorem source_meaning_export_code_meaning:
  source_meaning_decl_code FEMPTY source_meaning_export_meaning source_meaning_export_code
Proof
  assume_tac source_meaning_export_source >> assume_tac source_meaning_export_build >>
  drule_all source_meaning_declaration_transport >> strip_tac >> gvs[] >>
  `source_meaning_export_ctx.sm_env.type_defs = FEMPTY` by EVAL_TAC >> gvs[]
QED

Theorem source_meaning_export_module_meaning:
  LIST_REL (source_meaning_decl_code (type_env_all_modules source_meaning_aggregate_modules))
    [SDM_Constant "A" (BaseT (UintT 256)) (IntL 6);source_meaning_export_meaning]
    [VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 6)))
      "A" (BaseT (UintT 256)) NONE;source_meaning_export_code]
Proof
  `type_env_all_modules source_meaning_aggregate_modules = FEMPTY` by EVAL_TAC >>
  simp[source_meaning_export_code_meaning, source_meaning_decl_code_def,
    FUN_EQ_THM, Once evaluate_def, return_def, evaluate_literal_def]
QED

Theorem source_meaning_export_dispatch:
  ALOOKUP am.sources tx.target = SOME source_meaning_aggregate_modules /\
  ALOOKUP am.exports tx.target = SOME [("read",1)] /\ tx.function_name = "read" ==>
  let cx = initial_evaluation_context am.sources am.layouts tx (SOME 1) in
  call_external orc am tx =
    case source_meaning_invoke orc am cx
      [SDM_Constant "A" (BaseT (UintT 256)) (IntL 6);source_meaning_export_meaning]
      F Pure source_meaning_aggregate_modules [] [] tx.args
      [SBM_Return (SOME (SM_Literal (BaseT (UintT 256)) (IntL 6)))] (BaseT (UintT 256)) of
      (INL v,am',rqs) => (INL v,finalize_pending_deletions am',rqs)
    | failure => failure
Proof
  strip_tac >> irule source_meaning_exported_call_transport >> simp[] >> conj_tac
  >- simp[source_meaning_export_meaning_def, source_meaning_lookup_def] >>
  qexists_tac
    `[VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 6)))
      "A" (BaseT (UintT 256)) NONE;source_meaning_export_code]` >>
  conj_tac >- EVAL_TAC >> mp_tac source_meaning_export_module_meaning >> simp[]
QED

Theorem source_meaning_export_link_is_original:
  source_module_link source_meaning_aggregate_trust source_meaning_aggregate_registry
    source_meaning_aggregate_constants = SOME [("read",1)]
Proof
  EVAL_TAC
QED

val () = List.app (fn thy => List.app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("export source meaning audit: " ^ thy ^ "." ^ name) end) (DB.thms thy))
  ["sourceMeaningModules","sourceMeaningExportTest"];
