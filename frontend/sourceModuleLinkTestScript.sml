Theory sourceModuleLinkTest
Ancestors
  sourceModuleElaborate sourceModuleLink sourceModuleOverride sourceModuleEnv
  sourceModuleDefs sourceSyntax sourceConstAST sourceConstAnnotation sourceTypeDefs
  sourceResolveModules sourceResolve vyperAST vyperContext finite_map
Libs
  sourceModuleFrontendLib

Definition source_module_link_fixture_def:
  source_module_link_fixture = SourceProgram (SourceModule
    [SD_Import [SI_Import "lib" (SOME "l")];
     SD_Uses (SX_Name "l"); SD_Initializes (SX_Name "l");
     SD_Exports (SX_Attribute (SX_Name "l") "__interface__");
     SD_Function "f" [SX_Name "external"] [] [] (SOME (SCA_Name ["uint256"]))
       [SS_Return (SOME (SX_Call (SX_Attribute (SX_Name "l") "helper")
         [SX_Literal (SCL_Int 2)] []))]])
    [SourceModule
      [SD_Function "helper" [SX_Name "internal"]
         [SourceArg "x" (SOME (SCA_Name ["uint256"]))] [] (SOME (SCA_Name ["uint256"]))
         [SS_Return (SOME (SX_Name "x"))];
       SD_Function "visible" [SX_Name "external"] [] [] NONE [SS_Pass]]]
End

Definition source_module_link_trust_def:
  source_module_link_trust = <| smt_ids := [(["main"],NONE);(["lib"],SOME 1)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End

val linked = sourceModuleFrontendLib.check_simple
  {fuel=``30:num``,trust=``source_module_link_trust``,keys=``[["main"];["lib"]]``,
   program=``source_module_link_fixture``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val source_module_link_phase = save_thm ("source_module_link_phase",#equation (#elaboration linked));
val _ = save_thm ("source_module_link_check",#composition linked);
val _ = save_thm ("source_module_link_original",#original (#elaboration linked));
val _ = save_thm ("source_module_link_evidence",#linking (#elaboration linked));

Theorem source_module_link_call_exact:
  source_module_elaborate_simple 30 source_module_link_trust [["main"];["lib"]]
    source_module_link_fixture = SM_Ok (SourceRetained source_module_link_fixture
      [(NONE,[FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
        [Return (SOME (Call (BaseT (UintT 256)) (IntCall (SOME 1,"helper"))
          [Literal (BaseT (UintT 256)) (IntL 2)] NONE))]]);
       (SOME 1,[FunctionDecl Internal Nonpayable F F "helper" [("x",BaseT (UintT 256))]
          [] (BaseT (UintT 256)) [Return (SOME (Name (BaseT (UintT 256)) "x"))];
         FunctionDecl External Nonpayable F F "visible" [] [] NoneT [Pass]])])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV source_module_link_phase)) >> EVAL_TAC
QED

Theorem source_module_link_exports_exact:
  source_module_link source_module_link_trust
    [(["main"],SourceModule
      [SD_Import [SI_Import "lib" (SOME "l")];
       SD_Exports (SX_Attribute (SX_Name "l") "__interface__")]);
     (["lib"],SourceModule
       [SD_Function "visible" [SX_Name "external"] [] [] NONE [SS_Pass]])] [] =
    SOME [("visible",1)]
Proof
  EVAL_TAC
QED

Definition source_module_external_fixture_def:
  source_module_external_fixture = SourceProgram (SourceModule
    [SD_Interface "I" [SD_Function "read" [] [] [] (SOME (SCA_Name ["uint256"]))
      [SS_Expr (SX_Name "view")]];
     SD_Implements (SX_Name "I");
     SD_Function "read" [SX_Name "external";SX_Name "view"] [] []
       (SOME (SCA_Name ["uint256"])) [SS_Return (SOME (SX_Literal (SCL_Int 7)))];
     SD_Function "f" [SX_Name "external"]
       [SourceArg "target" (SOME (SCA_Name ["address"]))] [] (SOME (SCA_Name ["uint256"]))
       [SS_Return (SOME (SX_StaticCall (SX_Call
         (SX_Attribute (SX_Call (SX_Name "I") [SX_Name "target"] []) "read") []
         [("gas",SX_Binary SCB_Add (SX_Literal (SCL_Int 100)) (SX_Literal (SCL_Int 1)));
          ("skip_contract_check",SX_Literal (SCL_Bool T))])))];
     SD_Function "g" [SX_Name "external"]
       [SourceArg "target" (SOME (SCA_Name ["I"]))] [] (SOME (SCA_Name ["uint256"]))
       [SS_AnnAssign "i" (SCA_Name ["I"]) (SOME (SX_Name "target"));
        SS_Return (SOME (SX_StaticCall (SX_Call (SX_Attribute (SX_Name "i") "read") [] [])))]] ) []
End

val ext_trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [(["main";"I"],STI_Interface)];
  smt_type_defs := FEMPTY |+ ((NONE,"I"),InterfaceArgs
    [("read",[],BaseT (UintT 256),View)]); smt_slots := [] |>``;
val external = sourceModuleFrontendLib.check_simple
  {fuel=``40:num``,trust=ext_trust,keys=``[["main"]]``,program=``source_module_external_fixture``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val _ = save_thm ("source_module_external_phase",#equation (#elaboration external));
val _ = save_thm ("source_module_external_check",#composition external);
val _ = save_thm ("source_module_external_ast_exact",EQT_ELIM (EVAL (mk_eq
  (#modules (#elaboration external),
   ``[(NONE,[InterfaceDecl "I" [("read",[],BaseT (UintT 256),View)];
     FunctionDecl External View F F "read" [] [] (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))];
     FunctionDecl External Nonpayable F F "f" [("target",BaseT AddressT)] [] (BaseT (UintT 256))
       [Return (SOME (Call (BaseT (UintT 256))
         (ExtCall T T ("read",[],BaseT (UintT 256)) [EKGas])
         [Name (BaseT AddressT) "target";Literal (BaseT (UintT 256)) (IntL 101)] NONE))];
     FunctionDecl External Nonpayable F F "g" [("target",BaseT AddressT)] [] (BaseT (UintT 256))
       [AnnAssign "i" (BaseT AddressT) (Name (BaseT AddressT) "target");
        Return (SOME (Call (BaseT (UintT 256)) (ExtCall T F ("read",[],BaseT (UintT 256)) [])
          [Name (BaseT AddressT) "i"] NONE))]])] : (num option # toplevel list) list``))));

Definition source_module_mutating_fixture_def:
  source_module_mutating_fixture = SourceProgram (SourceModule
    [SD_Interface "I" [SD_Function "ping" [] [] [] NONE [SS_Expr (SX_Name "nonpayable")]];
     SD_Function "f" [SX_Name "external"]
       [SourceArg "target" (SOME (SCA_Name ["address"]))] [] NONE
       [SS_Expr (SX_ExtCall (SX_Call
         (SX_Attribute (SX_Call (SX_Name "I") [SX_Name "target"] []) "ping") []
         [("gas",SX_Literal (SCL_Int 77))]))]]) []
End

val mutating = sourceModuleFrontendLib.check_simple
  {fuel=``40:num``,keys=``[["main"]]``,program=``source_module_mutating_fixture``,
   trust=``<| smt_ids := [(["main"],NONE)]; smt_nominals := [(["main";"I"],STI_Interface)];
     smt_type_defs := FEMPTY |+ ((NONE,"I"),InterfaceArgs [("ping",[],NoneT,Nonpayable)]);
     smt_slots := [] |>``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val _ = save_thm ("source_module_mutating_phase",#equation (#elaboration mutating));
val _ = save_thm ("source_module_mutating_check",#composition mutating);
val _ = save_thm ("source_module_mutating_ast_exact",EQT_ELIM (EVAL (mk_eq
  (#modules (#elaboration mutating),
   ``[(NONE,[InterfaceDecl "I" [("ping",[],NoneT,Nonpayable)];
     FunctionDecl External Nonpayable F F "f" [("target",BaseT AddressT)] [] NoneT
       [Expr (Call NoneT (ExtCall F F ("ping",[],NoneT) [EKGas])
         [Name (BaseT AddressT) "target";Literal (BaseT (UintT 256)) (IntL 77)] NONE)]
     ])] :
       (num option # toplevel list) list``))));

Theorem source_module_default_structural_not_value:
  ~source_module_default_override ctx ctx
    (SOME (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))))
    (SOME (SX_Literal (SCL_Int 3)))
Proof
  EVAL_TAC
QED

Definition source_module_override_fixture_def:
  source_module_override_fixture abstract_default override_default = SourceProgram (SourceModule
    [SD_Import [SI_Import "lib" (SOME "l")]; SD_Initializes (SX_Name "l");
     SD_Function "helper" [SX_Name "internal";
       SX_Call (SX_Name "override") [SX_Name "l"] []]
       [SourceArg "x" (SOME (SCA_Name ["uint256"]))] [override_default]
       (SOME (SCA_Name ["uint256"])) [SS_Return (SOME (SX_Name "x"))];
     SD_Function "f" [SX_Name "external"] [] [] (SOME (SCA_Name ["uint256"]))
       [SS_Return (SOME (SX_Call (SX_Attribute (SX_Name "l") "helper") [] []))]])
    [SourceModule [SD_Function "helper" [SX_Name "abstract"]
      [SourceArg "x" (SOME (SCA_Name ["uint256"]))] [abstract_default]
      (SOME (SCA_Name ["uint256"])) [SS_Expr SX_Ellipsis]]]
End

val override_checked = sourceModuleFrontendLib.check_simple
  {fuel=``40:num``,trust=``source_module_link_trust``,keys=``[["main"];["lib"]]``,
   program=``source_module_override_fixture SX_Ellipsis (SX_Literal (SCL_Int 3))``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val _ = save_thm ("source_module_override_phase",#equation (#elaboration override_checked));
val _ = save_thm ("source_module_override_check",#composition override_checked);
val _ = save_thm ("source_module_override_links",#linking (#elaboration override_checked));

val source_module_override_mismatch_computation = save_thm
  ("source_module_override_mismatch_computation",EVAL
    ``source_module_link_program_simple source_module_link_trust [["main"];["lib"]]
      (source_module_override_fixture
        (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
        (SX_Literal (SCL_Int 3)))``);

Theorem source_module_override_rejects_folded_equality:
  source_module_elaborate_simple 40 source_module_link_trust [["main"];["lib"]]
    (source_module_override_fixture
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
      (SX_Literal (SCL_Int 3))) = SM_Error (SME_Declaration "source-linkage")
Proof
  simp[source_module_elaborate_simple_def,source_module_override_mismatch_computation,
       source_module_bind_def]
QED

val () = List.app (fn thy => List.app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("source module link kernel audit: " ^ thy ^ "." ^ name) end) (DB.thms thy))
  ["sourceModuleLink","sourceModuleOverride","sourceModuleLinkTest"];
