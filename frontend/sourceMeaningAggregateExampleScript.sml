Theory sourceMeaningAggregateExample
Ancestors
  sourceMeaningModules sourceMeaningPolicy sourceMeaningPolicyDecl sourceMeaningCall sourceMeaningCallDefs
  sourceMeaningDecl sourceMeaningProgram sourceMeaningProgramDefs sourceMeaningStmt
  sourceMeaningStmtDefs sourceMeaningRuntime sourceMeaningElaborate sourceMeaningCode
  sourceMeaningDefs sourceMeaningValue sourceMeaningConst sourceModuleElaborate
  sourceModuleDecl sourceModuleEnv sourceModuleDefs sourceResolveModules sourceResolve
  sourceSyntax sourceConstAST sourceConstAnnotation sourceConstValue sourceConstEnv
  vyperInterpreter vyperState vyperContext vyperAST vyperValue vyperTypeSystem finite_map alist list
Libs
  sourceModuleFrontendLib intLib wordsLib

Definition source_meaning_aggregate_annotation_def:
  source_meaning_aggregate_annotation = SCA_Tuple
    [SCA_Name ["uint256"]; SCA_StaticArray (SCA_Name ["uint256"])
      (SCE_Literal (SCL_Int 2))]
End
Definition source_meaning_aggregate_original_def:
  source_meaning_aggregate_original = SX_Tuple
    [SX_Attribute (SX_Name "l") "A";
     SX_List [SX_Attribute (SX_Name "l") "A"; SX_Literal (SCL_Int 7)]]
End
Definition source_meaning_aggregate_registry_input_def:
  source_meaning_aggregate_registry_input =
    [(["main"],SourceModule
      [SD_Import [SI_Import "lib" (SOME "l")];
       SD_Uses (SX_Name "l"); SD_Initializes (SX_Name "l");
       SD_Exports (SX_Attribute (SX_Name "l") "read");
       SD_Variable "PAIR" (SCA_Qualified SCQ_Constant source_meaning_aggregate_annotation)
         (SOME source_meaning_aggregate_original);
       SD_Function "pair" [SX_Name "external";SX_Name "pure"] [] []
         (SOME source_meaning_aggregate_annotation) [SS_Return (SOME (SX_Name "PAIR"))]]);
     (["lib"],SourceModule
      [SD_Import [SI_Import "base" (SOME "b")];
       SD_Variable "A" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
         (SOME (SX_Binary SCB_Mul (SX_Attribute (SX_Name "b") "N") (SX_Literal (SCL_Int 2))));
       SD_Function "read" [SX_Name "external";SX_Name "pure"] [] []
         (SOME (SCA_Name ["uint256"])) [SS_Return (SOME (SX_Name "A"))]]);
     (["base"],SourceModule
      [SD_Variable "N" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
         (SOME (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))))])]
End
Definition source_meaning_aggregate_registry_def:
  source_meaning_aggregate_registry =
    [HD source_meaning_aggregate_registry_input;
     EL 2 source_meaning_aggregate_registry_input;
     EL 1 source_meaning_aggregate_registry_input]
End
Definition source_meaning_aggregate_program_def:
  source_meaning_aggregate_program = SourceProgram
    (SND (HD source_meaning_aggregate_registry))
    (MAP SND (TL source_meaning_aggregate_registry))
End
Definition source_meaning_aggregate_trust_def:
  source_meaning_aggregate_trust = <|
    smt_ids := [(["main"],NONE);(["base"],SOME 2);(["lib"],SOME 1)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End
Definition source_meaning_aggregate_policies_def:
  source_meaning_aggregate_policies =
    [(["main"],SourceModulePolicy F F);(["base"],SourceModulePolicy F F);
     (["lib"],SourceModulePolicy F F)]
End
Definition source_meaning_aggregate_type_def:
  source_meaning_aggregate_type = TupleT
    [BaseT (UintT 256);ArrayT (BaseT (UintT 256)) (Fixed 2)]
End
Definition source_meaning_aggregate_value_def:
  source_meaning_aggregate_value = SCV_Tuple [SCV_Int 6;SCV_List [SCV_Int 6;SCV_Int 7]]
End

val elaborated = sourceModuleFrontendLib.elaborate
  {fuel=``20:num``,trust=``source_meaning_aggregate_trust``,
   policies=``source_meaning_aggregate_policies``,keys=``[["main"];["base"];["lib"]]``,
   program=``source_meaning_aggregate_program``};
val _ = save_thm ("source_meaning_aggregate_phase",#equation elaborated);
val _ = save_thm ("source_meaning_aggregate_link",#linking elaborated);
val _ = save_thm ("source_meaning_aggregate_public_transport",
  MATCH_MP source_meaning_policy_elaborate_member (#equation elaborated));
val _ = save_thm ("source_meaning_aggregate_policy_program_transport",
  MATCH_MP source_meaning_policy_program_transport (#equation elaborated));
val _ = Define `source_meaning_aggregate_modules = ^(#modules elaborated)`;

Theorem source_meaning_aggregate_resolved:
  source_resolve_program_registry source_meaning_aggregate_program
    [["main"];["base"];["lib"]] = SOME source_meaning_aggregate_registry /\
  source_resolve_registry_constants source_meaning_aggregate_registry =
    SOME (SCEnv_Resolved
      [(["base";"N"],SC_Constant (SCV_Int 3));
       (["lib";"A"],SC_Constant (SCV_Int 6));
       (["main";"PAIR"],SC_Constant source_meaning_aggregate_value)])
Proof
  EVAL_TAC
QED

Definition source_meaning_aggregate_constants_def:
  source_meaning_aggregate_constants =
    [(["base";"N"],SC_Constant (SCV_Int 3));
     (["lib";"A"],SC_Constant (SCV_Int 6));
     (["main";"PAIR"],SC_Constant source_meaning_aggregate_value)]
End
Definition source_meaning_aggregate_ctx_def:
  source_meaning_aggregate_ctx = source_module_context source_meaning_aggregate_trust
    source_meaning_aggregate_registry source_meaning_aggregate_constants ["main"]
    (SND (HD source_meaning_aggregate_registry))
End

val source_meaning_aggregate_ctx_evaluated = save_thm
  ("source_meaning_aggregate_ctx_evaluated",EVAL ``source_meaning_aggregate_ctx``);

Theorem source_meaning_aggregate_source:
  source_meaning_source [] source_meaning_aggregate_ctx.sm_scopes
    source_meaning_aggregate_ctx.sm_table source_meaning_aggregate_ctx.sm_constants
    source_meaning_aggregate_type (SX_Name "PAIR")
    (SM_Constant source_meaning_aggregate_type source_meaning_aggregate_value)
Proof
  irule sourceMeaningDefsTheory.aggregate >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_aggregate_dependency_meaning:
  source_meaning_constants source_meaning_aggregate_registry source_meaning_aggregate_constants
Proof
  irule source_meaning_program_constants_transport >>
  simp[source_meaning_aggregate_constants_def, source_meaning_aggregate_resolved]
QED

Theorem source_meaning_aggregate_body_source:
  source_meaning_bodies [] source_meaning_aggregate_ctx source_meaning_aggregate_type
    [SS_Return (SOME (SX_Name "PAIR"))]
    [SBM_Return (SOME (SM_Constant source_meaning_aggregate_type source_meaning_aggregate_value))]
    [] source_meaning_aggregate_ctx
Proof
  irule sourceMeaningStmtDefsTheory.cons >> qexistsl_tac [`source_meaning_aggregate_ctx`,`[]`] >>
  simp[sourceMeaningStmtDefsTheory.empty] >>
  irule sourceMeaningStmtDefsTheory.return_value >> simp[source_meaning_aggregate_source]
QED
