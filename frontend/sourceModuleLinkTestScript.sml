Theory sourceModuleLinkTest
Ancestors
  sourceModuleContext sourceModuleLink sourceModuleOverride sourceModuleEnv
  sourceModuleDefs sourceSyntax sourceConstAST sourceConstAnnotation sourceTypeDefs
  sourceResolveModules sourceResolve vyperAST vyperContext finite_map

Definition source_module_link_trust_def:
  source_module_link_trust = <| smt_ids := [(["main"],NONE);(["lib"],SOME 1)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End

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

(* Original defaults, not folded equality, control override compatibility.
   This exercises linkage directly without elaborating executable bodies. *)
val source_module_override_mismatch_computation = save_thm
  ("source_module_override_mismatch_computation",EVAL
    ``source_module_link_program source_module_link_trust
      [(["main"],source_module_policy_default);(["lib"],source_module_policy_default)]
      [["main"];["lib"]] (source_module_override_fixture
        (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
        (SX_Literal (SCL_Int 3)))``);

Theorem source_module_override_rejects_folded_equality:
  source_module_link_program source_module_link_trust
    [(["main"],source_module_policy_default);(["lib"],source_module_policy_default)]
    [["main"];["lib"]] (source_module_override_fixture
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
      (SX_Literal (SCL_Int 3))) = SM_Error (SME_Declaration "source-linkage")
Proof
  ACCEPT_TAC source_module_override_mismatch_computation
QED

val () = List.app (fn thy => List.app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("source module link kernel audit: " ^ thy ^ "." ^ name) end) (DB.thms thy))
  ["sourceModuleLink","sourceModuleOverride","sourceModuleLinkTest"];
