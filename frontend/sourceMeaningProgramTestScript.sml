Theory sourceMeaningProgramTest
Ancestors
  sourceMeaningExample sourceMeaningExampleDefs sourceMeaningProgram sourceMeaningProgramDefs
  sourceMeaningStmt sourceMeaningStmtDefs sourceMeaningTest sourceMeaningDefs sourceMeaningConst
  sourceModuleElaborate sourceModuleDecl sourceModuleEnv sourceModuleDefs sourceSyntax
  sourceConstAnnotation vyperInterpreter vyperState vyperContext vyperAST vyperValue finite_map
Libs
  intLib wordsLib

Theorem source_meaning_example_entry:
  source_meaning_entry source_meaning_example_program [["main"]]
    source_meaning_example_registry ["main"] source_meaning_example_syntax
    source_meaning_example_decl source_meaning_example_ctx source_meaning_example_types
    (BaseT (UintT 256)) source_meaning_example_terms
Proof
  simp[source_meaning_entry_def, source_meaning_example_resolved,
    source_meaning_example_constants_meaning, source_meaning_example_ctx_fields] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  qexistsl_tac [`"f"`,`[SX_Name "external";SX_Name "pure"]`,
    `[SourceArg "x" (SOME source_meaning_example_uint);
      SourceArg "flag" (SOME (SCA_Name ["bool"]))]`, `[]`,
    `SOME source_meaning_example_uint`, `source_meaning_example_body`,
    `[("x",BaseT (UintT 256));("flag",BaseT BoolT)]`,
    `source_meaning_example_ytypes`, `source_meaning_example_yctx`] >>
  simp[GSYM source_meaning_example_decl_def] >> rpt conj_tac
  >- EVAL_TAC >- EVAL_TAC >>
  `source_module_function_context source_meaning_example_ctx "f"
    [SourceArg "x" (SOME source_meaning_example_uint);
     SourceArg "flag" (SOME (SCA_Name ["bool"]))]
    [("x",BaseT (UintT 256));("flag",BaseT BoolT)] = source_meaning_example_fctx` by EVAL_TAC >>
  simp[source_meaning_example_source]
QED

Theorem source_meaning_example_function_build:
  source_module_body 12 source_meaning_example_ctx [] source_meaning_example_decl =
    SM_Ok [FunctionDecl External Pure F F "f"
      [("x",BaseT (UintT 256));("flag",BaseT BoolT)] [] (BaseT (UintT 256))
      source_meaning_example_code]
Proof
  EVAL_TAC
QED

Theorem source_meaning_example_link:
  source_module_link_program_simple source_meaning_example_trust [["main"]]
    source_meaning_example_program = SM_Ok
    (source_meaning_example_registry,source_meaning_example_constants,[],[])
Proof
  `source_module_trust_ok source_meaning_example_registry source_meaning_example_trust`
    by EVAL_TAC >>
  `source_module_link source_meaning_example_trust source_meaning_example_registry
    source_meaning_example_constants = SOME []` by EVAL_TAC >>
  `source_module_overrides source_meaning_example_trust source_meaning_example_registry
    source_meaning_example_constants = SOME []` by EVAL_TAC >>
  simp[source_module_link_program_simple_def, source_meaning_example_resolved]
QED

Theorem source_meaning_example_module_build:
  source_module_elaborate_simple 12 source_meaning_example_trust [["main"]]
    source_meaning_example_program =
  SM_Ok (SourceRetained source_meaning_example_program [(NONE,
    [VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 3))) "N"
      (BaseT (UintT 256)) NONE;
     FunctionDecl External Pure F F "f"
      [("x",BaseT (UintT 256));("flag",BaseT BoolT)] [] (BaseT (UintT 256))
      source_meaning_example_code])])
Proof
  simp[source_module_elaborate_simple_def, source_meaning_example_link, source_module_bind_def] >>
  `source_module_signature_modules 12 source_meaning_example_trust
      source_meaning_example_registry source_meaning_example_constants = SM_Ok [(NONE,
    [VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 3))) "N"
      (BaseT (UintT 256)) NONE;
     FunctionDecl External Pure F F "f"
      [("x",BaseT (UintT 256));("flag",BaseT BoolT)] [] (BaseT (UintT 256)) []])]` by EVAL_TAC >>
  simp[source_module_elaborate_registry_def, source_module_bind_def] >> EVAL_TAC
QED

Definition source_meaning_example_initial_def:
  source_meaning_example_initial flag st = st with <| abi_memory := [];
    scopes := [FEMPTY |+ ("x",<| assignable := T; type := BaseTV (UintT 256); value := IntV 4 |>)
      |+ ("flag",<| assignable := T; type := BaseTV BoolT; value := BoolV flag |>)] |>
End

Theorem source_meaning_example_behavior:
  !flag st. source_meaning_execute empty_evaluation_context source_meaning_example_terms
    (source_meaning_example_initial flag st) =
    (INR (ReturnException (IntV (if flag then 7 else 3))),
     (source_meaning_example_initial flag st) with scopes :=
       [FEMPTY |+ ("x",<| assignable := T; type := BaseTV (UintT 256); value := IntV 4 |>)
        |+ ("flag",<| assignable := T; type := BaseTV BoolT; value := BoolV flag |>)
        |+ ("y",<| assignable := T; type := BaseTV (UintT 256);
                   value := IntV (if flag then 7 else 3) |>)])
Proof
  Cases >> gen_tac >> EVAL_TAC >> simp[]
QED

fun audit_source_program thy =
  let val exports = DB.thms thy
      fun check (name,th) = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
        in if null (hyp th) andalso null axioms andalso
          List.all (fn tag => tag = "DISK_THM") oracles then ()
          else raise Fail ("source program kernel audit: " ^ thy ^ "." ^ name) end
  in List.app check exports;
     print ("SOURCE_PROGRAM_KERNEL_CLOSED " ^ thy ^ " exports=" ^
       Int.toString (length exports) ^ "\n") end;

val () = List.app audit_source_program
  ["sourceMeaningConst","sourceMeaningDefs","sourceMeaningCode","sourceMeaningElaborate",
   "sourceMeaningEffects","sourceMeaningRuntime","sourceMeaningTest",
   "sourceMeaningStmtDefs","sourceMeaningStmt","sourceMeaningEnv","sourceMeaningProgramDefs",
   "sourceMeaningProgram","sourceMeaningExampleDefs","sourceMeaningExample","sourceMeaningProgramTest"];
