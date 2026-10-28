Theory sourceOrdinaryProgram
Ancestors
  sourceOrdinaryDecl sourceOrdinaryClaims sourceModuleElaborate sourceModuleOverride
  sourceModuleDefs sourceModuleEnv sourceSyntax jsonToVyper jsonToVyperExpr
  jsonAST vyperTypeContract list pair option alist

(* Explicit inherited runtime type/import/dispatch contexts. No runtime bodies
   or folded values enter via these contexts. Source declaration types and
   bounds, constants, defaults and iteration bounds are not inherited. *)
Definition source_ordinary_registry_def:
  source_ordinary_registry fuel trust policies contexts roots registry constants links =
    source_module_bind (source_module_policy_signature_modules fuel trust policies registry constants)
      (\signatures.
      if type_env_all_modules signatures <> trust.smt_type_defs then
        SM_Error (SME_Declaration "nominal-environment") else
      source_module_collect (MAP (\(i,(owner,syntax)).
        let ctx = source_module_policy_body_context trust policies registry constants signatures owner syntax;
            path = if i = 0 then [0] else [1;i-1] in
        case (source_module_override_bindings trust links ctx.sm_bindings,ALOOKUP contexts owner) of
          (SOME bindings,SOME legacy) => source_module_bind
            (source_ordinary_declarations fuel roots path (ctx with sm_bindings := bindings)
              legacy trust.smt_slots (source_module_policy_for policies owner) syntax)
            (\tls. case ALOOKUP trust.smt_ids owner of SOME src => SM_Ok (src,tls)
              | NONE => SM_Error SME_Resolution)
        | _ => SM_Error (SME_Declaration "inherited-runtime-context"))
        (ZIP (GENLIST I (LENGTH registry),registry))))
End

Definition source_ordinary_program_def:
  source_ordinary_program fuel trust policies keys contexts program claims =
    if source_program_claims_source claims <> program \/ ~source_program_claims_shape claims then
      SM_Error (SME_Declaration "program-pairing") else
    source_module_bind (source_module_link_program trust policies keys program)
      (\(registry,constants,exports,links).
      source_module_bind (source_ordinary_registry fuel trust policies contexts
        (source_program_claims_roots claims) registry constants links)
        (\modules. SM_Ok (SourceRetained program modules)))
End

Theorem source_ordinary_program_retains_source:
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained ==>
  retained_source retained = program
Proof
  simp[source_ordinary_program_def,AllCaseEqs()] >> strip_tac >>
  drule source_module_bind_success >> strip_tac >>
  rename1 `source_module_link_program trust policies keys program = SM_Ok data` >>
  PairCases_on `data` >> fs[] >> drule source_module_bind_retains_source >> simp[]
QED

Theorem source_ordinary_program_pairing:
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained ==>
  source_program_claims_source claims = program /\ source_program_claims_shape claims
Proof
  simp[source_ordinary_program_def,AllCaseEqs()]
QED

Theorem source_ordinary_program_linkage:
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained ==>
  ?registry constants exports links.
    source_module_link_program trust policies keys program = SM_Ok (registry,constants,exports,links)
Proof
  simp[source_ordinary_program_def,AllCaseEqs()] >> strip_tac >>
  drule source_module_bind_success >> strip_tac >>
  rename1 `source_module_link_program trust policies keys program = SM_Ok data` >>
  PairCases_on `data` >> metis_tac[]
QED

Definition source_ordinary_check_def:
  source_ordinary_check fuel trust policies keys contexts program claims layouts address =
    source_module_bind (source_ordinary_program fuel trust policies keys contexts program claims)
      (\retained. case check_contract T layouts address (retained_executable retained) of
         SOME art => SM_Ok (retained,art) | NONE => SM_Error SME_Check)
End

Theorem source_ordinary_check_equations:
  source_ordinary_check fuel trust policies keys contexts program claims layouts address =
    SM_Ok (retained,art) ==>
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained /\
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art
Proof
  simp[source_ordinary_check_def] >>
  Cases_on `source_ordinary_program fuel trust policies keys contexts program claims` >>
  simp[source_module_bind_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule source_ordinary_program_retains_source >> simp[]
QED

(* The backend callback receives exactly the checked modules, including
   deployment bodies. No flattening of module identities or retranslation. *)
Definition source_ordinary_compile_def:
  source_ordinary_compile compiler fuel trust policies keys contexts program claims layouts address =
    source_module_bind
      (source_ordinary_check fuel trust policies keys contexts program claims layouts address)
      (\(retained,art). case compiler (retained_executable retained) of
         SOME bytes => SM_Ok (retained,art,bytes)
       | NONE => SM_Error (SME_Declaration "backend-compilation"))
End

Theorem source_ordinary_compile_equations:
  source_ordinary_compile compiler fuel trust policies keys contexts program claims layouts address =
    SM_Ok (retained,art,bytes) ==>
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained /\
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art /\
  compiler (retained_executable retained) = SOME bytes
Proof
  simp[source_ordinary_compile_def] >>
  Cases_on `source_ordinary_check fuel trust policies keys contexts program claims layouts address` >>
  simp[source_module_bind_def] >>
  rename1 `source_ordinary_check fuel trust policies keys contexts program claims layouts address = SM_Ok checked` >>
  PairCases_on `checked` >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule source_ordinary_check_equations >> simp[]
QED

(* Build the inherited expression contexts WITHOUT translating any body or
   initializer. This is a convenience for legacy import/type claims, not source
   inference. Callers explicitly opt into this remaining trust. *)
Definition source_ordinary_legacy_contexts_def:
  source_ordinary_legacy_contexts identities ast =
    case canonicalize_annotated_ast_imports ast of
      JAnnotatedAST (JModule main nr tops) imports =>
      let indexes = build_import_compact_indexes imports;
          maps = build_import_maps_from_indexes indexes;
          nominals = build_nominal_index tops imports;
          overrides = build_override_map tops imports;
          types = build_all_toplevel_types nominals maps main tops imports;
          make = \src body. (main,(src,(build_import_map (collect_imports body),
              (collect_consts_and_immutables body,([], (types,overrides))))));
          contexts = (NONE,make NONE tops) :: MAP (\imp.
            case imp of JImportedModule src path resolved nr body =>
              (SOME (source_id_to_module_id src),make (SOME (source_id_to_module_id src)) body)) imports
      in if EVERY (\(src,ctx). EVERY (\(sid,cx). src = sid ==> ctx = cx) contexts) contexts then
        OPT_MMAP (\(owner,src). OPTION_MAP (\ctx. (owner,ctx)) (ALOOKUP contexts src)) identities
      else NONE
End
