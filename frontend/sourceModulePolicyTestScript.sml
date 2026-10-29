Theory sourceModulePolicyTest
Ancestors
  sourceModuleContext sourceModuleSignature sourceModuleDefs sourceSyntax

(* Shared legality/policy checks, independent of executable body production. *)
Theorem missing_policy_registry_rejected:
  source_module_link_program trust [] [["main"]] program =
    SM_Error (SME_Declaration "policy-registry")
Proof
  simp[source_module_link_program_def]
QED

Theorem nonreentrant_policy_not_inferred:
  source_module_policy_signature 10 ctx [] (SourceModulePolicy T F)
    (SD_Function "f" [SX_Name "external";SX_Name "reentrant"] [] [] NONE [SS_Pass]) =
  source_module_policy_signature 10 ctx [] (SourceModulePolicy F F)
    (SD_Function "f" [SX_Name "external";SX_Name "reentrant"] [] [] NONE [SS_Pass])
Proof
  simp[source_module_policy_signature_def, source_module_declaration_only_def,
    source_module_nonreentrant_default_def]
QED

Theorem declaration_only_rejects_implementation:
  source_module_policy_signature 10 ctx [] (SourceModulePolicy F T)
    (SD_Function "f" [SX_Name "external"] [] [] NONE [SS_Pass]) =
    SM_Error (SME_Declaration "interface-signature")
Proof
  simp[source_module_policy_signature_def, source_module_declaration_only_def]
QED
