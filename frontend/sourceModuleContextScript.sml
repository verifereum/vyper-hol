Theory sourceModuleContext
Ancestors
  sourceModuleSignature sourceModuleLink sourceModuleOverride sourceModuleEnv sourceModuleDefs
  sourceResolveModules sourceConstEnv sourceSyntax sourceExprDefs sourceTypeDefs
  vyperTypeContract vyperContext vyperAST list alist
Libs
  intLib

(* Shared signature and runtime contexts. No statement/body elaboration occurs
   here: ordinary occurrence-paired normalization consumes these contexts. *)
Definition source_module_signature_context_def:
  source_module_signature_context trust registry constants signatures owner syntax =
    let ctx = source_module_context trust registry constants owner syntax in
    let art = build_contract_type_artifact T signatures in
    ctx with <| sm_env := artifact_env art signatures ctx.sm_env.current_src;
      sm_bindings := FLAT (MAP (\(key,src).
        source_module_runtime_bindings trust.smt_ids key
          (case ALOOKUP signatures src of SOME tls => tls | NONE => [])) trust.smt_ids) ++
        ctx.sm_bindings;
      sm_events := FLAT (MAP (\(key,src).
        source_module_event_bindings trust.smt_ids key
          (case ALOOKUP signatures src of SOME tls => tls | NONE => [])) trust.smt_ids) |>
End

Definition source_module_policy_signature_modules_def:
  source_module_policy_signature_modules fuel trust policies registry constants =
    source_module_collect (MAP (\(owner,syntax).
      source_module_bind (source_module_policy_signatures fuel
        (source_module_policy_context trust policies registry constants owner syntax)
        trust.smt_slots (source_module_policy_for policies owner) syntax)
        (\tls. case ALOOKUP trust.smt_ids owner of NONE => SM_Error SME_Resolution
         | SOME src => SM_Ok (src,tls))) registry)
End

Definition source_module_policy_signature_context_def:
  source_module_policy_signature_context trust policies registry constants signatures owner syntax =
    let ctx = source_module_signature_context trust registry constants signatures owner syntax in
    let annotations = source_module_policy_context trust policies registry constants owner syntax in
    ctx with <| sm_names := annotations.sm_names;
      sm_bindings := FLAT (MAP (\(key,p).
        if source_module_declaration_only p then
          case ALOOKUP trust.smt_ids key of NONE => [] | SOME src =>
            [(key,SE_Interface (FLAT (MAP (\tl. case tl of
              FunctionDecl vis mut nr raw name params defaults ret body => [(name,params,ret,mut)]
              | _ => []) (case ALOOKUP signatures src of SOME tls => tls | NONE => []))))]
        else []) policies) ++ ctx.sm_bindings |>
End

Definition source_module_link_program_def:
  source_module_link_program trust policies keys program =
    if MAP FST policies <> keys then SM_Error (SME_Declaration "policy-registry") else
    case source_resolve_program_registry program keys of
      NONE => SM_Error SME_Resolution
    | SOME registry =>
        if ~source_module_trust_ok registry trust then SM_Error SME_Resolution else
        case source_resolve_registry_constants registry of
          SOME (SCEnv_Resolved constants) =>
            (case (source_module_link trust registry constants,
                   source_module_policy_overrides trust policies registry constants) of
               (SOME exports,SOME links) =>
                 if source_module_policy_link_ok trust policies exports then
                   SM_Ok (registry,constants,exports,links)
                 else SM_Error (SME_Declaration "interface-export")
             | _ => SM_Error (SME_Declaration "source-linkage"))
        | SOME err => SM_Error (SME_Dependencies err)
        | NONE => SM_Error SME_Resolution
End

Theorem source_module_link_program_equations:
  source_module_link_program trust policies keys program = SM_Ok (registry,constants,exports,links) ==>
  MAP FST policies = keys /\
  source_resolve_program_registry program keys = SOME registry /\
  source_module_trust_ok registry trust /\
  source_resolve_registry_constants registry = SOME (SCEnv_Resolved constants) /\
  source_module_link trust registry constants = SOME exports /\
  source_module_policy_overrides trust policies registry constants = SOME links /\
  source_module_policy_link_ok trust policies exports
Proof
  simp[source_module_link_program_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem source_module_bind_success:
  source_module_bind result f = SM_Ok y ==>
  ?x. result = SM_Ok x /\ f x = SM_Ok y
Proof
  Cases_on `result` >> simp[source_module_bind_def]
QED

Theorem source_module_bind_retains_source:
  source_module_bind result (\modules. SM_Ok (SourceRetained program modules)) =
    SM_Ok retained ==> retained_source retained = program
Proof
  Cases_on `result` >> simp[source_module_bind_def] >> rw[] >> simp[retained_source_def]
QED
