Theory sourceModuleBoundaryTest
Ancestors
  sourceModuleElaborate sourceModuleDecl sourceModuleEnv sourceModuleDefs
  sourceModuleStmt sourceSyntax sourceConstAST sourceConstAnnotation
  sourceTypeDefs sourceResolveModules sourceResolve sourceConstEnv
  vyperTypeContract vyperAST vyperContext finite_map
Libs
  sourceModuleFrontendLib

Definition source_module_import_fixture_def:
  source_module_import_fixture = SourceProgram (SourceModule
    [SD_Import [SI_Import "lib" (SOME "l")];
     SD_Variable "A" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
       (SOME (SX_Binary SCB_Add (SX_Attribute (SX_Name "l") "B") (SX_Literal (SCL_Int 1))));
     SD_Function "f" [SX_Name "external"] [] [] (SOME (SCA_Name ["uint256"]))
       [SS_Return (SOME (SX_Name "A"))]])
    [SourceModule
      [SD_Variable "B" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
        (SOME (SX_Binary SCB_Add (SX_Name "C") (SX_Literal (SCL_Int 1))));
       SD_Variable "C" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
        (SOME (SX_Literal (SCL_Int 1)))]]
End

Definition source_module_import_trust_def:
  source_module_import_trust = <| smt_ids := [(["main"],NONE);(["lib"],SOME 1)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End

val imported = sourceModuleFrontendLib.check_simple
  {fuel=``30:num``,trust=``source_module_import_trust``,keys=``[["main"];["lib"]]``,
   program=``source_module_import_fixture``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val source_module_import_phase = save_thm ("source_module_import_phase",
  #equation (#elaboration imported));

Theorem source_module_import_forward_exact:
  source_module_elaborate_simple 30 source_module_import_trust [["main"];["lib"]]
    source_module_import_fixture =
  SM_Ok (SourceRetained source_module_import_fixture
    [(NONE,[VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 3)))
              "A" (BaseT (UintT 256)) NONE;
            FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
              [Return (SOME (Literal (BaseT (UintT 256)) (IntL 3)))]]);
     (SOME 1,[VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 2)))
                "B" (BaseT (UintT 256)) NONE;
              VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 1)))
                "C" (BaseT (UintT 256)) NONE])])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV source_module_import_phase)) >> EVAL_TAC
QED

val _ = save_thm ("source_module_import_forward_check", #composition imported);

Definition source_module_bound_fixture_def:
  source_module_bound_fixture = SourceProgram (SourceModule
    [SD_Function "f" [SX_Name "external"]
      [SourceArg "n" (SOME (SCA_Name ["uint256"]))] [] (SOME (SCA_Name ["uint256"]))
      [SS_For "i" (SCA_Name ["uint256"])
        (SX_Call (SX_Name "range") [SX_Name "n"]
          [("bound",SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))])
        [SS_Pass];
       SS_Return (SOME (SX_Name "n"))];
     SD_Variable "data" (SCA_StaticArray (SCA_Name ["uint256"])
       (SCE_Binary SCB_Add (SCE_Binary SCB_RShift
         (SCE_Binary SCB_LShift (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 256)))
         (SCE_Literal (SCL_Int 255))) (SCE_Literal (SCL_Int 1)))) NONE]) []
End

val bounded = sourceModuleFrontendLib.elaborate_simple
  {fuel=``40:num``,trust=``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := [((NONE,"data"),0)] |> ``,
   keys=``[["main"]]``,program=``source_module_bound_fixture``};
val source_module_bound_phase = save_thm ("source_module_bound_phase", #equation bounded);

Theorem source_module_source_bounds_exact:
  source_module_elaborate_simple 40
    <| smt_ids := [(["main"],NONE)]; smt_nominals := []; smt_type_defs := FEMPTY;
       smt_slots := [((NONE,"data"),0)] |> [["main"]] source_module_bound_fixture =
  SM_Ok (SourceRetained source_module_bound_fixture
    [(NONE,[FunctionDecl External Nonpayable F F "f" [("n",BaseT (UintT 256))] []
              (BaseT (UintT 256))
              [For "i" (BaseT (UintT 256))
                 (Range (Literal (BaseT (UintT 256)) (IntL 0)) (Name (BaseT (UintT 256)) "n"))
                 3 [Pass];Return (SOME (Name (BaseT (UintT 256)) "n"))];
            VariableDecl Private Storage "data" (ArrayT (BaseT (UintT 256)) (Fixed 3)) (SOME 0)])])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV source_module_bound_phase)) >> EVAL_TAC
QED

Definition source_module_event_fixture_def:
  source_module_event_fixture = SourceProgram (SourceModule
    [SD_Event "Changed" [SourceArg "value" (SOME
       (SCA_Qualified SCQ_Indexed (SCA_Name ["uint256"])))];
     SD_Function "f" [SX_Name "external"] [] [] NONE
       [SS_Log (SX_Call (SX_Name "Changed")
         [SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))] [])]]) []
End

val event_checked = sourceModuleFrontendLib.check_simple
  {fuel=``30:num``,trust=``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := [] |> ``,keys=``[["main"]]``,
   program=``source_module_event_fixture``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val _ = save_thm ("source_module_event_check", #composition event_checked);
val source_module_event_phase = save_thm ("source_module_event_phase",
  #equation (#elaboration event_checked));

Theorem source_module_event_exact:
  source_module_elaborate_simple 30
    <| smt_ids := [(["main"],NONE)]; smt_nominals := []; smt_type_defs := FEMPTY;
       smt_slots := [] |> [["main"]] source_module_event_fixture =
  SM_Ok (SourceRetained source_module_event_fixture
    [(NONE,[EventDecl "Changed" [(("value",BaseT (UintT 256)),T)];
            FunctionDecl External Nonpayable F F "f" [] [] NoneT
              [vyperAST$Log (NONE,"Changed") [Literal (BaseT (UintT 256)) (IntL 3)]]])])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV source_module_event_phase)) >> EVAL_TAC
QED

val source_module_missing_name_computation = save_thm ("source_module_missing_name_computation",
  EVAL ``source_module_elaborate_simple 20
    <| smt_ids := [(["main"],NONE)]; smt_nominals := []; smt_type_defs := FEMPTY;
       smt_slots := [] |> [["main"]]
    (SourceProgram (SourceModule
      [SD_Function "f" [SX_Name "external"] [] [] (SOME (SCA_Name ["uint256"]))
        [SS_Return (SOME (SX_Name "unknown"))]]) [])``);

Theorem source_module_missing_name_not_dynamic:
  source_module_elaborate_simple 20
    <| smt_ids := [(["main"],NONE)]; smt_nominals := []; smt_type_defs := FEMPTY;
       smt_slots := [] |> [["main"]]
    (SourceProgram (SourceModule
      [SD_Function "f" [SX_Name "external"] [] [] (SOME (SCA_Name ["uint256"]))
        [SS_Return (SOME (SX_Name "unknown"))]]) []) =
  SM_Error (SME_Unsupported (SCS_Syntax "expression-resolution"))
Proof
  ACCEPT_TAC source_module_missing_name_computation
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source module boundary kernel audit: " ^ name) end)
  (DB.thms "sourceModuleBoundaryTest");
