Theory sourceModuleElaborate
Ancestors
  sourceModuleContext sourceModuleSignature sourceModuleDecl sourceModuleLink sourceModuleOverride sourceModuleEnv sourceModuleDefs sourceResolveModules
  sourceConstEnv sourceSyntax sourceExprDefs sourceTypeDefs vyperTypeContract vyperContext vyperAST list alist
Libs
  intLib

(* Policy-free helpers keep their original equations for the independent source
   meaning development. Shared contexts/signatures also serve the ordinary path. *)
Definition source_module_signature_modules_def:
  source_module_signature_modules fuel trust registry constants =
    source_module_collect (MAP (\(owner,syntax).
      source_module_bind (source_module_signatures fuel
        (source_module_context trust registry constants owner syntax) trust.smt_slots syntax)
        (\tls. case ALOOKUP trust.smt_ids owner of
           NONE => SM_Error SME_Resolution | SOME src => SM_Ok (src,tls))) registry)
End

Definition source_module_elaborate_registry_def:
  source_module_elaborate_registry fuel trust registry constants links =
    source_module_bind (source_module_signature_modules fuel trust registry constants) (\signatures.
      if type_env_all_modules signatures <> trust.smt_type_defs then
        SM_Error (SME_Declaration "nominal-environment") else
      source_module_collect (MAP (\(owner,syntax).
        let ctx = source_module_signature_context trust registry constants signatures owner syntax in
        case source_module_override_bindings trust links ctx.sm_bindings of
          NONE => SM_Error (SME_Declaration "override-cycle")
        | SOME bindings => source_module_bind (source_module_bodies fuel
          (ctx with sm_bindings := bindings) trust.smt_slots syntax) (\tls.
            case ALOOKUP trust.smt_ids owner of NONE => SM_Error SME_Resolution
            | SOME src => SM_Ok (src,tls))) registry))
End

Definition source_module_link_program_simple_def:
  source_module_link_program_simple trust keys program =
    case source_resolve_program_registry program keys of
      NONE => SM_Error SME_Resolution
    | SOME registry =>
        if ~source_module_trust_ok registry trust then SM_Error SME_Resolution else
        case source_resolve_registry_constants registry of
          SOME (SCEnv_Resolved constants) =>
            (case (source_module_link trust registry constants,
                   source_module_overrides trust registry constants) of
               (SOME exports,SOME links) => SM_Ok (registry,constants,exports,links)
             | _ => SM_Error (SME_Declaration "source-linkage"))
        | SOME err => SM_Error (SME_Dependencies err)
        | NONE => SM_Error SME_Resolution
End

Definition source_module_elaborate_simple_def:
  source_module_elaborate_simple fuel trust keys program =
    source_module_bind (source_module_link_program_simple trust keys program)
      (\(registry,constants,exports,links).
        source_module_bind (source_module_elaborate_registry fuel trust registry constants links)
          (\modules. SM_Ok (SourceRetained program modules)))
End

Theorem source_module_link_program_simple_equations:
  source_module_link_program_simple trust keys program = SM_Ok (registry,constants,exports,links) ==>
  source_resolve_program_registry program keys = SOME registry /\
  source_module_trust_ok registry trust /\
  source_resolve_registry_constants registry = SOME (SCEnv_Resolved constants) /\
  source_module_link trust registry constants = SOME exports /\
  source_module_overrides trust registry constants = SOME links
Proof
  simp[source_module_link_program_simple_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem source_module_elaborate_simple_linkage:
  source_module_elaborate_simple fuel trust keys program = SM_Ok retained ==>
  ?registry constants exports links.
    source_module_link_program_simple trust keys program = SM_Ok (registry,constants,exports,links) /\
    source_module_link trust registry constants = SOME exports /\
    source_module_overrides trust registry constants = SOME links
Proof
  simp[source_module_elaborate_simple_def] >> strip_tac >>
  drule source_module_bind_success >> strip_tac >>
  rename1 `source_module_link_program_simple trust keys program = SM_Ok data` >>
  PairCases_on `data` >> gvs[] >>
  drule source_module_link_program_simple_equations >> strip_tac >> metis_tac[]
QED

Definition source_module_check_simple_def:
  source_module_check_simple fuel trust keys program layouts address =
    source_module_bind (source_module_elaborate_simple fuel trust keys program) (\retained.
      case check_contract T layouts address (retained_executable retained) of
        NONE => SM_Error SME_Check
      | SOME art => SM_Ok (retained,art))
End

Theorem source_module_elaborate_simple_retains_source:
  source_module_elaborate_simple fuel trust keys program = SM_Ok retained ==>
  retained_source retained = program
Proof
  simp[source_module_elaborate_simple_def] >> strip_tac >>
  drule source_module_bind_success >> strip_tac >>
  rename1 `source_module_link_program_simple trust keys program = SM_Ok data` >>
  PairCases_on `data` >> fs[] >>
  drule source_module_bind_retains_source >> simp[]
QED

Theorem source_module_check_simple_equations:
  source_module_check_simple fuel trust keys program layouts address = SM_Ok (retained,art) ==>
  source_module_elaborate_simple fuel trust keys program = SM_Ok retained /\
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art
Proof
  simp[source_module_check_simple_def] >>
  Cases_on `source_module_elaborate_simple fuel trust keys program` >>
  simp[source_module_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule source_module_elaborate_simple_retains_source >> simp[]
QED

(* ===== Explicit preserved policies ===== *)
Definition source_module_policy_elaborate_registry_def:
  source_module_policy_elaborate_registry fuel trust policies registry constants links =
    source_module_bind (source_module_policy_signature_modules fuel trust policies registry constants)
      (\signatures.
      if type_env_all_modules signatures <> trust.smt_type_defs then
        SM_Error (SME_Declaration "nominal-environment") else
      source_module_collect (MAP (\(owner,syntax).
        let ctx = source_module_policy_signature_context trust policies registry constants signatures owner syntax in
        case source_module_override_bindings trust links ctx.sm_bindings of
          NONE => SM_Error (SME_Declaration "override-cycle")
        | SOME bindings => source_module_bind (source_module_policy_bodies fuel
            (ctx with sm_bindings := bindings) trust.smt_slots
            (source_module_policy_for policies owner) syntax) (\tls.
            case ALOOKUP trust.smt_ids owner of NONE => SM_Error SME_Resolution
            | SOME src => SM_Ok (src,tls))) registry))
End

Definition source_module_elaborate_def:
  source_module_elaborate fuel trust policies keys program =
    source_module_bind (source_module_link_program trust policies keys program)
      (\(registry,constants,exports,links).
        source_module_bind (source_module_policy_elaborate_registry fuel trust policies registry constants links)
          (\modules. SM_Ok (SourceRetained program modules)))
End

Theorem source_module_elaborate_linkage:
  source_module_elaborate fuel trust policies keys program = SM_Ok retained ==>
  ?registry constants exports links.
    source_module_link_program trust policies keys program = SM_Ok (registry,constants,exports,links) /\
    source_module_link trust registry constants = SOME exports /\
    source_module_policy_overrides trust policies registry constants = SOME links
Proof
  simp[source_module_elaborate_def] >> strip_tac >>
  drule source_module_bind_success >> strip_tac >>
  rename1 `source_module_link_program trust policies keys program = SM_Ok data` >>
  PairCases_on `data` >> gvs[] >>
  drule source_module_link_program_equations >> strip_tac >> metis_tac[]
QED

Theorem source_module_elaborate_retains_source:
  source_module_elaborate fuel trust policies keys program = SM_Ok retained ==>
  retained_source retained = program
Proof
  simp[source_module_elaborate_def] >> strip_tac >>
  drule source_module_bind_success >> strip_tac >>
  rename1 `source_module_link_program trust policies keys program = SM_Ok data` >>
  PairCases_on `data` >> fs[] >> drule source_module_bind_retains_source >> simp[]
QED

Definition source_module_check_def:
  source_module_check fuel trust policies keys program layouts address =
    source_module_bind (source_module_elaborate fuel trust policies keys program) (\retained.
      case check_contract T layouts address (retained_executable retained) of
        NONE => SM_Error SME_Check
      | SOME art => SM_Ok (retained,art))
End

Theorem source_module_check_equations:
  source_module_check fuel trust policies keys program layouts address = SM_Ok (retained,art) ==>
  source_module_elaborate fuel trust policies keys program = SM_Ok retained /\
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art
Proof
  simp[source_module_check_def] >>
  Cases_on `source_module_elaborate fuel trust policies keys program` >>
  simp[source_module_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule source_module_elaborate_retains_source >> simp[]
QED
