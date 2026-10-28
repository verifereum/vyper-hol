Theory sourceMeaningCallExampleDefs
Ancestors
  sourceMeaningCompile sourceMeaningDispatch sourceMeaningDecl sourceMeaningCall
  sourceMeaningCallDefs sourceMeaningStmtDefs sourceMeaningDefs sourceModuleElaborate
  sourceModuleEnv sourceModuleDecl sourceModuleDefs sourceSyntax sourceConstAST
  sourceConstAnnotation sourceConstEnv vyperAST vyperValue vyperState vyperContext finite_map

Definition source_meaning_call_uint_def:
  source_meaning_call_uint = BaseT (UintT 256)
End
Definition source_meaning_call_annotation_def:
  source_meaning_call_annotation = SCA_Name ["uint256"]
End
Definition source_meaning_call_initializer_def:
  source_meaning_call_initializer = SX_Binary SCB_Add
    (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))
End
Definition source_meaning_call_function_def:
  source_meaning_call_function = SD_Function "f" [SX_Name "external";SX_Name "pure"]
    [SourceArg "x" (SOME source_meaning_call_annotation)] [SX_Name "N"]
    (SOME source_meaning_call_annotation)
    [SS_Return (SOME (SX_Binary SCB_Add (SX_Name "x") (SX_Name "N")))]
End
Definition source_meaning_call_syntax_def:
  source_meaning_call_syntax = SourceModule
    [SD_Variable "N" (SCA_Qualified SCQ_Constant source_meaning_call_annotation)
      (SOME source_meaning_call_initializer); source_meaning_call_function]
End
Definition source_meaning_call_registry_def:
  source_meaning_call_registry = [(["main"],source_meaning_call_syntax)]
End
Definition source_meaning_call_constants_def:
  source_meaning_call_constants = [(["main";"N"],SC_Constant (SCV_Int 3))]
End
Definition source_meaning_call_trust_def:
  source_meaning_call_trust = <| smt_ids := [(["main"],NONE)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := [] |>
End
Definition source_meaning_call_signature_def:
  source_meaning_call_signature =
    [VariableDecl Private (Constant (Literal source_meaning_call_uint (IntL 3))) "N"
       source_meaning_call_uint NONE;
     FunctionDecl External Pure F F "f" [("x",source_meaning_call_uint)]
       [Literal NoneT (IntL 0)] source_meaning_call_uint []]
End
Definition source_meaning_call_ctx_def:
  source_meaning_call_ctx = source_module_body_context source_meaning_call_trust
    source_meaning_call_registry source_meaning_call_constants
    [(NONE,source_meaning_call_signature)] ["main"] source_meaning_call_syntax
End
Definition source_meaning_call_fctx_def:
  source_meaning_call_fctx = source_module_function_context source_meaning_call_ctx "f"
    [SourceArg "x" (SOME source_meaning_call_annotation)] [("x",source_meaning_call_uint)]
End
Definition source_meaning_call_types_def:
  source_meaning_call_types = source_meaning_parameter_types source_meaning_call_ctx "f"
    [SourceArg "x" (SOME source_meaning_call_annotation)] [("x",source_meaning_call_uint)]
End
Definition source_meaning_call_body_def:
  source_meaning_call_body =
    [SBM_Return (SOME (SM_Binary source_meaning_call_uint SCB_Add
      (SM_Name source_meaning_call_uint ["main";"f";"x"])
      (SM_Literal source_meaning_call_uint (IntL 3))))]
End
Definition source_meaning_call_denotation_def:
  source_meaning_call_denotation =
    [SDM_Constant "N" source_meaning_call_uint (IntL 3);
     SDM_Function External Pure F F "f" [("x",source_meaning_call_uint)]
       [SM_Literal source_meaning_call_uint (IntL 3)] source_meaning_call_uint
       source_meaning_call_body]
End
Definition source_meaning_call_tops_def:
  source_meaning_call_tops =
    [VariableDecl Private (Constant (Literal source_meaning_call_uint (IntL 3))) "N"
       source_meaning_call_uint NONE;
     FunctionDecl External Pure F F "f" [("x",source_meaning_call_uint)]
       [Literal source_meaning_call_uint (IntL 3)] source_meaning_call_uint
       [Return (SOME (Builtin source_meaning_call_uint (Bop Add)
         [Name source_meaning_call_uint "x"; Literal source_meaning_call_uint (IntL 3)]))]]
End
Definition source_meaning_call_ctor_source_def:
  source_meaning_call_ctor_source = SD_Function "__init__" [SX_Name "deploy";SX_Name "payable"]
    [SourceArg "x" (SOME source_meaning_call_annotation)] [SX_Name "N"] NONE [SS_Pass]
End
Definition source_meaning_call_ctor_meaning_def:
  source_meaning_call_ctor_meaning = SDM_Function Deploy Payable F F "__init__"
    [("x",source_meaning_call_uint)] [SM_Literal source_meaning_call_uint (IntL 3)] NoneT [SBM_Pass]
End
Definition source_meaning_call_ctor_code_def:
  source_meaning_call_ctor_code = FunctionDecl Deploy Payable F F "__init__"
    [("x",source_meaning_call_uint)] [Literal source_meaning_call_uint (IntL 3)] NoneT [Pass]
End
Definition source_meaning_call_machine_def:
  source_meaning_call_machine = initial_machine_state with
    sources := [(0w,[(NONE,source_meaning_call_tops)])]
End
