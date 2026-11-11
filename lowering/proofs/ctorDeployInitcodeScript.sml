(* Initcode size bounds for codegen_correct's initial_ctx_rel.
 * TOP-LEVEL: deploy_initcode_half_bounded (LENGTH code <= dimword(:256)
 * DIV 2, which code_layout_valid needs).
 * Helpers: bind_arguments_values_typed, classify_functions_ctor_lookup,
 * constructor_args_size_bounded.
 * The code is deploy_bc ++ args_bytes (deploy_state_rel). deploy_bc is below
 * 65536 bytes (deploy_bc_size_bounded). args_bytes is the ABI encoding of
 * the typed constructor arguments, so at most their ABI size bound, which
 * fn_allocs_ok keeps below 2 ** 128 for the constructor the compiler
 * packages; that constructor is lookup_function's "__init__".
 *)
Theory ctorDeployInitcode
Ancestors
  ctorDeployDefs ctorDeployInitcodeAsm compileVyper compileEnv
  abiTypeBoundProps vyperTypeABI vyperTyping structFieldsProps
  vyperTypeContractStaticMaps loweringHalt vyperInterpreter vyperABI
  e2eDeployDefs vyperTypeContract option

(* Arguments bind_arguments accepts are typed by their parameters' types. *)
Theorem bind_arguments_values_typed:
  !tenv params vs scope.
    bind_arguments tenv params vs = SOME scope ==>
    ?tvs. LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
            (MAP SND params) tvs /\
          values_have_types tvs vs
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def, value_has_type_def] >>
  gvs[AllCaseEqs()] >>
  qexists_tac `tv :: tvs` >> simp[value_has_type_def] >>
  metis_tac[safe_cast_some_eq, safe_cast_result_well_typed]
QED

(* The constructor classify_functions picks is the first Deploy function;
   when it has the name looked up, lookup_function returns it, and with no
   Deploy function lookup_function returns the empty default constructor. *)
Theorem classify_functions_ctor_lookup:
  !tops src name.
    case SND (SND (SND (classify_functions tops))) of
      NONE =>
        vyperInterpreter$lookup_function src name Deploy tops =
          SOME (Payable, F, [], [], NoneT, [])
    | SOME (fmut, fnr, frr, fname, fargs, fdflts, fret, fbody) =>
        fname = name ==>
        vyperInterpreter$lookup_function src name Deploy tops =
          SOME (fmut, fnr, fargs, fdflts, fret, fbody)
Proof
  Induct >- simp[classify_functions_def, vyperInterpreterTheory.lookup_function_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`src`, `name`] mp_tac) >>
  simp[classify_functions_def] >>
  `?a b c d. FOLDR classify_function ([],[],NONE,NONE) tops = (a,b,c,d)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  simp[] >> strip_tac >>
  Cases_on `h` >>
  simp[classify_function_def, vyperInterpreterTheory.lookup_function_def]
  >~ [`VariableDecl vd`]
  >- (Cases_on `vd` >> simp[vyperInterpreterTheory.lookup_function_def])
  >~ [`HashMapDecl hd`]
  >- (Cases_on `hd` >> simp[vyperInterpreterTheory.lookup_function_def]) >>
  qmatch_goalsub_rename_tac `case vv of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vv` >> rw[]
QED

(* The constructor's appended arguments are below 2 ** 128 bytes. *)
Theorem constructor_args_size_bounded:
  !policy tops deploy_bc runtime_bc arts am tx bs.
    deploy_phases policy tops (deploy_bc, runtime_bc) arts /\
    deploy_source_ok tops am tx /\
    constructor_args_encode tops tx bs
    ==>
    LENGTH bs < 2 ** 128
Proof
  rpt gen_tac >> PairCases_on `arts` >>
  rw[deploy_phases_def, deploy_source_ok_def, constructor_args_encode_def] >>
  gvs[IS_SOME_EXISTS] >>
  drule bind_arguments_values_typed >> strip_tac >>
  drule_all (cj 2 vyper_to_abi_enc_length_bound) >> strip_tac >>
  `sfields_tenv_consistent (make_struct_fields_map tops) (type_env tops)` by (
    irule make_struct_fields_map_consistent >>
    gvs[deploy_typing_ok_def, check_contract_def] >>
    drule contract_namespaces_ok_module_type_def_keys >> simp[]) >>
  `EVERY (\t. IS_SOME (evaluate_type (type_env tops) t)) (MAP SND args)` by (
    gvs[listTheory.EVERY_MEM, listTheory.LIST_REL_EL_EQN,
        listTheory.MEM_EL, PULL_EXISTS] >>
    rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all abi_size_bound_tuple_typed >> strip_tac >>
  `vyper_abi_size_bound (type_env tops) (TupleT (MAP SND args)) =
   vyper_abi_size_bound_list (type_env tops) (MAP SND args)` by
    simp[Once vyper_abi_size_bound_def] >>
  `abi_size_bound (make_struct_fields_map tops) (TupleT (MAP SND args)) <
   2 ** 128` suffices_by (strip_tac >> fs[] >> decide_tac) >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >>
  Cases_on `r2` >> simp[]
  >- (rpt strip_tac >> gvs[abi_size_bound_def]) >>
  qmatch_goalsub_rename_tac `ctor_named_init (SOME cf)` >>
  PairCases_on `cf` >> simp[ctor_named_init_def] >> rpt strip_tac >>
  `fn_allocs_ok tops (cf0,cf1,cf2,cf3,cf4,cf5,cf6,cf7)` by (
    irule lower_vyper_deploy_unit_allocs_ok >> simp[] >>
    metis_tac[]) >>
  gvs[fn_allocs_ok_def, build_compile_env_ce_struct_fields]
QED

Theorem deploy_initcode_half_bounded:
  !policy tops deploy_bc runtime_bc arts am tx es.
    deploy_phases policy tops (deploy_bc, runtime_bc) arts /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    LENGTH (FST (HD es.contexts)).msgParams.code <= dimword(:256) DIV 2
Proof
  rpt strip_tac >>
  drule_all deploy_bc_size_bounded >> strip_tac >>
  gvs[deploy_state_rel_def] >>
  drule_all constructor_args_size_bounded >>
  simp[wordsTheory.dimword_def]
QED
