Theory sourceMeaningExampleDefs
Ancestors
  sourceMeaningProgram sourceMeaningProgramDefs sourceMeaningStmt sourceMeaningStmtDefs
  sourceMeaningDefs sourceMeaningConst sourceMeaningRuntime
  sourceModuleDecl sourceModuleEnv sourceModuleDefs sourceModuleStmt sourceSyntax
  sourceResolveModules sourceResolve sourceExprDefs sourceConstAST sourceConstAnnotation
  sourceConstEnv sourceConstEval sourceConstValue vyperInterpreter vyperTypeSystem vyperTypeContract
  vyperState vyperContext vyperAST vyperValue finite_map alist list
Libs
  intLib wordsLib

Definition source_meaning_example_uint_def:
  source_meaning_example_uint = SCA_Name ["uint256"]
End
Definition source_meaning_example_body_def:
  source_meaning_example_body =
    [SS_AnnAssign "y" source_meaning_example_uint (SOME (SX_Name "N"));
     SS_If (SX_Name "flag")
       [SS_Assign (SX_Name "y") (SX_Binary SCB_Add (SX_Name "x") (SX_Name "N"))]
       [SS_Assign (SX_Name "y") (SX_Name "N")];
     SS_Return (SOME (SX_Name "y"))]
End
Definition source_meaning_example_decl_def:
  source_meaning_example_decl = SD_Function "f" [SX_Name "external";SX_Name "pure"]
    [SourceArg "x" (SOME source_meaning_example_uint);
     SourceArg "flag" (SOME (SCA_Name ["bool"]))] []
    (SOME source_meaning_example_uint) source_meaning_example_body
End
Definition source_meaning_example_syntax_def:
  source_meaning_example_syntax = SourceModule
    [SD_Variable "N" (SCA_Qualified SCQ_Constant source_meaning_example_uint)
       (SOME (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))));
     source_meaning_example_decl]
End
Definition source_meaning_example_program_def:
  source_meaning_example_program = SourceProgram source_meaning_example_syntax []
End
Definition source_meaning_example_registry_def:
  source_meaning_example_registry = [(["main"],source_meaning_example_syntax)]
End
Definition source_meaning_example_constants_def:
  source_meaning_example_constants = [(["main";"N"],SC_Constant (SCV_Int 3))]
End
Definition source_meaning_example_trust_def:
  source_meaning_example_trust = <| smt_ids := [(["main"],NONE)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End
Definition source_meaning_example_ctx_def:
  source_meaning_example_ctx = source_module_context source_meaning_example_trust
    source_meaning_example_registry source_meaning_example_constants ["main"]
      source_meaning_example_syntax
End
Definition source_meaning_example_fctx_def:
  source_meaning_example_fctx = source_module_local
    (source_module_local (source_meaning_example_ctx with sm_owner := ["main";"f"])
      "x" (BaseT (UintT 256)) T) "flag" (BaseT BoolT) T
End
Definition source_meaning_example_yctx_def:
  source_meaning_example_yctx =
    source_module_local source_meaning_example_fctx "y" (BaseT (UintT 256)) T
End
Definition source_meaning_example_types_def:
  source_meaning_example_types =
    [(["main";"f";"flag"],BaseT BoolT);(["main";"f";"x"],BaseT (UintT 256))]
End
Definition source_meaning_example_ytypes_def:
  source_meaning_example_ytypes =
    (["main";"f";"y"],BaseT (UintT 256))::source_meaning_example_types
End
Definition source_meaning_example_terms_def:
  source_meaning_example_terms =
    [SBM_Local "y" (BaseT (UintT 256)) (SM_Literal (BaseT (UintT 256)) (IntL 3));
     SBM_If (SM_Name (BaseT BoolT) ["main";"f";"flag"])
       [SBM_Assign "y" (SM_Binary (BaseT (UintT 256)) SCB_Add
         (SM_Name (BaseT (UintT 256)) ["main";"f";"x"])
         (SM_Literal (BaseT (UintT 256)) (IntL 3)))]
       [SBM_Assign "y" (SM_Literal (BaseT (UintT 256)) (IntL 3))];
     SBM_Return (SOME (SM_Name (BaseT (UintT 256)) ["main";"f";"y"]))]
End
Definition source_meaning_example_code_def:
  source_meaning_example_code =
    [AnnAssign "y" (BaseT (UintT 256)) (Literal (BaseT (UintT 256)) (IntL 3));
     If (Name (BaseT BoolT) "flag")
       [Assign (BaseTarget (NameTarget "y"))
         (Builtin (BaseT (UintT 256)) (Bop Add)
           [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)])]
       [Assign (BaseTarget (NameTarget "y")) (Literal (BaseT (UintT 256)) (IntL 3))];
     Return (SOME (Name (BaseT (UintT 256)) "y"))]
End

Theorem source_meaning_example_ctx_fields[compute]:
  source_meaning_example_ctx.sm_scopes =
    source_module_scopes ["main"] source_meaning_example_syntax /\
  source_meaning_example_ctx.sm_table =
    source_resolve_table source_meaning_example_registry ++ source_module_extra_prelude /\
  source_meaning_example_ctx.sm_constants = source_meaning_example_constants
Proof
  simp[source_meaning_example_ctx_def, source_module_context_def]
QED

Theorem source_meaning_example_fctx_fields[compute]:
  source_meaning_example_fctx.sm_scopes =
    [[("flag",["main";"f";"flag"])];[("x",["main";"f";"x"])]] ++
      source_meaning_example_ctx.sm_scopes /\
  source_meaning_example_fctx.sm_table =
    [(["main";"f";"flag"],SR_Dynamic);(["main";"f";"x"],SR_Dynamic)] ++
      source_meaning_example_ctx.sm_table /\
  source_meaning_example_fctx.sm_constants = source_meaning_example_constants
Proof
  simp[source_meaning_example_fctx_def, source_module_local_def,
    source_meaning_example_ctx_fields]
QED

Theorem source_meaning_example_yctx_fields[compute]:
  source_meaning_example_yctx.sm_scopes =
    [("y",["main";"f";"y"]) ]::source_meaning_example_fctx.sm_scopes /\
  source_meaning_example_yctx.sm_table =
    (["main";"f";"y"],SR_Dynamic)::source_meaning_example_fctx.sm_table /\
  source_meaning_example_yctx.sm_constants = source_meaning_example_constants
Proof
  `source_meaning_example_fctx.sm_owner = ["main";"f"]` by EVAL_TAC >>
  simp[source_meaning_example_yctx_def, source_module_local_def,
    source_meaning_example_fctx_fields]
QED

Theorem source_meaning_example_resolved:
  source_resolve_program_registry source_meaning_example_program [["main"]] =
    SOME source_meaning_example_registry /\
  source_resolve_registry_constants source_meaning_example_registry =
    SOME (SCEnv_Resolved source_meaning_example_constants)
Proof
  EVAL_TAC
QED

Theorem source_meaning_example_constants_meaning:
  source_meaning_constants source_meaning_example_registry source_meaning_example_constants
Proof
  irule source_meaning_program_constants_transport >> simp[source_meaning_example_resolved]
QED

Theorem source_meaning_example_local_context:
  source_meaning_locals source_meaning_example_types source_meaning_example_fctx
Proof
  rw[source_meaning_locals_def, source_meaning_example_types_def, AllCaseEqs()] >> EVAL_TAC
QED

Theorem source_meaning_example_ytypes_context:
  source_meaning_example_ytypes =
    ((source_meaning_example_fctx.sm_owner ++ ["y"],BaseT (UintT 256))::source_meaning_example_types)
Proof
  EVAL_TAC
QED
