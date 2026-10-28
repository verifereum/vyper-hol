Theory sourceMeaningDispatch
Ancestors
  sourceMeaningDecl sourceMeaningCall sourceMeaningCallDefs sourceMeaningProgram
  sourceMeaningProgramDefs sourceMeaningStmt sourceMeaningStmtDefs
  sourceModuleCompile sourceModuleElaborate sourceModuleDecl sourceModuleDefs
  sourceSyntax vyperInterpreter vyperState vyperContext vyperAST alist list pair option

Theorem source_meaning_collect_declarations:
  !originals meanings.
  LIST_REL (source_meaning_declaration ctx) originals meanings ==>
  !emitted. source_module_collect
    (MAP (source_module_body fuel ctx slots) originals) = SM_Ok emitted ==>
  LIST_REL (source_meaning_decl_code ctx.sm_env.type_defs) meanings (FLAT emitted)
Proof
  Induct >> Cases_on `meanings` >> simp[source_module_collect_def] >>
  rpt gen_tac >> simp[source_meaning_bind_success] >> rpt strip_tac >> gvs[] >>
  drule_all source_meaning_declaration_transport >> strip_tac >> gvs[]
QED

Theorem source_meaning_module_transport:
  source_meaning_module ctx syntax meanings /\
  source_module_bodies fuel ctx slots syntax = SM_Ok tops ==>
  LIST_REL (source_meaning_decl_code ctx.sm_env.type_defs) meanings tops
Proof
  simp[source_meaning_module_def, source_module_bodies_def,
    source_meaning_bind_success] >> rpt strip_tac >> gvs[] >>
  drule_all source_meaning_collect_declarations >> simp[]
QED

(* Source name dispatch, not a selection from erased code. This instance has
   one source module and no export redirection; imports/getters need more source
   rules. It includes normal functions, explicit constructors and empty default
   constructors. Runtime values at the API are already ABI-decoded. *)
Definition source_meaning_call_def:
  source_meaning_call orc am tx meanings =
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
    case ALOOKUP am.sources tx.target of
      NONE => (INR (Error (RuntimeError "call get sources")),am,[])
    | SOME mods =>
      case source_meaning_lookup tx.function_name External meanings of
        NONE => (INR (Error (RuntimeError "call lookup_function")),am,[])
      | SOME (mut,nr,args,dms,ret,bms) =>
        case source_meaning_invoke orc am cx meanings nr mut mods args dms tx.args bms ret of
          (INL v,am',rqs) => (INL v,finalize_pending_deletions am',rqs)
        | failure => failure
End

Definition source_meaning_load_def:
  source_meaning_load orc am tx mods exps meanings =
    let addr = tx.target in
    let am = am with <| immutables updated_by CONS (addr,empty_immutables);
                        exports updated_by CONS (addr,exps) |> in
    case source_meaning_lookup tx.function_name Deploy meanings of
      NONE => INR (Error (RuntimeError "no constructor"))
    | SOME (mut,nr,args,dms,ret,bms) =>
      let cx = (initial_evaluation_context ((addr,mods)::am.sources) am.layouts tx NONE)
        with in_deploy := T in
      case source_meaning_invoke orc am cx meanings nr mut mods args dms tx.args bms ret of
        (INR e,_,_) => INR e
      | (_,am',rqs) => INL (finalize_pending_deletions
          (am' with sources updated_by CONS (addr,mods)),rqs)
End

Theorem source_meaning_call_transport:
  ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
  ALOOKUP am.exports tx.target = NONE /\
  LIST_REL (source_meaning_decl_code (type_env_all_modules [(NONE,tops)])) meanings tops ==>
  call_external orc am tx = source_meaning_call orc am tx meanings
Proof
  strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `get_tenv cx = type_env_all_modules [(NONE,tops)]` by
    simp[Abbr`cx`, get_tenv_def, initial_evaluation_context_def] >>
  drule source_meaning_lookup_transport >>
  disch_then (qspecl_then [`tx.function_name`,`External`] mp_tac) >>
  Cases_on `source_meaning_lookup tx.function_name External meanings` >>
  simp[OPTREL_def] >> strip_tac
  >- simp[call_external_def, source_meaning_call_def, find_function_module_def,
      lookup_exported_function_def, get_self_code_def, get_module_code_def,
      initial_evaluation_context_def, Abbr`cx`] >>
  rename1 `source_meaning_lookup _ _ _ = SOME source_entry` >>
  rename1 `lookup_function _ _ _ _ = SOME runtime_entry` >>
  PairCases_on `source_entry` >> PairCases_on `runtime_entry` >> gvs[] >>
  `LIST_REL (source_meaning_decl_code (get_tenv cx)) meanings tops` by simp[] >>
  first_x_assum drule >> strip_tac >>
  drule_all source_meaning_invoke_transport >> strip_tac >>
  simp[call_external_def, source_meaning_call_def, find_function_module_def,
    lookup_exported_function_def, get_self_code_def, get_module_code_def,
    initial_evaluation_context_def, Abbr`cx`] >>
  gvs[initial_evaluation_context_def]
QED

(* The independent source instance has no immutable declarations. Establish
   that fact from the source-derived code relation, instead of asking the source
   evaluator to inspect runtime declarations to allocate its cells. *)
Theorem source_meaning_initial_immutables_module:
  !meanings tops. LIST_REL (source_meaning_decl_code tenv) meanings tops ==>
  !env src acc. initial_immutables_module env src tops acc = SOME acc
Proof
  Induct >> Cases_on `tops` >> simp[initial_immutables_module_def] >>
  gen_tac >> strip_tac >> rename1 `source_meaning_decl_code _ m tl` >>
  Cases_on `m` >> gvs[source_meaning_decl_code_def] >>
  simp[initial_immutables_module_def]
QED

Theorem source_meaning_initial_immutables:
  LIST_REL (source_meaning_decl_code tenv) meanings tops ==>
  initial_immutables env [(NONE,tops)] = SOME empty_immutables
Proof
  strip_tac >> simp[initial_immutables_def] >>
  drule source_meaning_initial_immutables_module >> simp[]
QED

Theorem source_meaning_load_transport:
  LIST_REL (source_meaning_decl_code (type_env_all_modules [(NONE,tops)])) meanings tops ==>
  load_contract orc am tx [(NONE,tops)] exps =
    source_meaning_load orc am tx [(NONE,tops)] exps meanings
Proof
  strip_tac >>
  drule source_meaning_initial_immutables >> strip_tac >>
  drule source_meaning_lookup_transport >>
  disch_then (qspecl_then [`tx.function_name`,`Deploy`] mp_tac) >>
  simp[OPTREL_def] >>
  Cases_on `source_meaning_lookup tx.function_name Deploy meanings` >> simp[] >>
  strip_tac >> simp[load_contract_def, source_meaning_load_def] >>
  rename1 `source_meaning_lookup _ _ _ = SOME source_entry` >>
  rename1 `lookup_function _ _ _ _ = SOME runtime_entry` >>
  PairCases_on `source_entry` >> PairCases_on `runtime_entry` >> gvs[] >>
  simp[load_contract_def, source_meaning_load_def] >>
  qabbrev_tac `am0 = am with <| immutables := (tx.target,empty_immutables)::am.immutables;
    exports := (tx.target,exps)::am.exports |>` >>
  qabbrev_tac `cx = (initial_evaluation_context
    ((tx.target,[(NONE,tops)])::am0.sources) am0.layouts tx NONE) with in_deploy := T` >>
  `get_tenv cx = type_env_all_modules [(NONE,tops)]` by
    simp[Abbr`cx`, get_tenv_def, initial_evaluation_context_def] >>
  `LIST_REL (source_meaning_decl_code (get_tenv cx)) meanings tops` by simp[] >>
  first_x_assum drule >> strip_tac >>
  drule_all source_meaning_invoke_transport >> strip_tac >>
  gvs[Abbr`cx`, Abbr`am0`]
QED
