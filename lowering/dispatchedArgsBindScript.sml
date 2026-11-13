(*
 * The values vyperCalldata's calldata_dispatch decodes for an external
 * function have its parameters' types, so they bind.
 *
 * TOP-LEVEL:
 *   dispatched_vyper_call_bind
 *)
Theory dispatchedArgsBind
Ancestors
  vyperCalldata supportedProgram vyperInterpreter e2eDefs
  dispatchedSignatureArgs dispatchedDecodeDomain dispatchedDecodeCast
  vyperTypeContract entryDispatchProps supportedNames list

Theorem bind_arguments_cast_fixed[local]:
  !args tvs vals. OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs /\
    LIST_REL (\tv v. safe_cast tv v = SOME v) tvs vals ==>
    ?env. bind_arguments tenv args vals = SOME env
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vals` >>
  simp[bind_arguments_def] >> rpt gen_tac >>
  rename1 `SND arg` >> PairCases_on `arg` >> simp[] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  `?env. bind_arguments tenv args t' = SOME env` by metis_tac[] >>
  simp[bind_arguments_def]
QED

Theorem dispatched_selector_args_bind:
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (name,tys) (abi_external_signatures tops) /\
  OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
  calldata_decode_args calldata tvs 0 = SOME vals /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?env. bind_arguments (type_env tops) args vals = SOME env
Proof
  rpt strip_tac >> drule_all dispatched_signature_args >> strip_tac >> gvs[] >>
  drule evaluate_types_cd_cast_domain >> strip_tac >>
  drule_all calldata_decode_args_safe_cast >> strip_tac >>
  irule bind_arguments_cast_fixed >> goal_assum (drule_at Any) >> simp[]
QED

Theorem dispatched_fallback_args_bind:
  supported_program tops /\ source_typing_ok tops am tx /\
  EXISTS is_default_decl tops /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?env. bind_arguments (type_env tops) args [] = SOME env
Proof
  rpt strip_tac >>
  gvs[source_typing_ok_def, EXISTS_MEM] >>
  drule check_contract_external_names_distinct >>
  simp[contract_keys_def] >> strip_tac >>
  qpat_x_assum `is_default_decl _` mp_tac >>
  Cases_on `e` >> simp[is_default_decl_def] >>
  Cases_on `f` >> simp[is_default_decl_def] >> rpt strip_tac >> gvs[] >>
  `function_header_ok External f0 b b0 "__default__" l l0 t` by
    metis_tac[check_contract_function_header, MEM] >>
  drule supported_fallback_no_arguments >> strip_tac >> gvs[] >>
  `lookup_function NONE "__default__" External tops =
     SOME (f0,b,[],l0,t,l1)` by
    (irule lookup_function_external_unique_decl >> conj_tac >- simp[] >>
     qexists_tac `FunctionDecl External f0 b b0 "__default__" [] l0 t l1` >>
     simp[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def]) >>
  gvs[bind_arguments_def]
QED

Theorem dispatched_vyper_call_bind:
  !tops calldata name vals mut args ret fbody am tx.
    supported_program tops /\
    source_typing_ok tops am tx /\
    calldata_dispatch tops calldata = SOME (name, vals) /\
    vyperInterpreter$lookup_function NONE name External tops =
      SOME (mut, F, args, [], ret, fbody) ==>
    ?env. bind_arguments (type_env tops) args vals = SOME env
Proof
  rpt strip_tac >>
  gvs[calldata_dispatch_def, AllCaseEqs()] >>
  metis_tac[dispatched_fallback_args_bind, dispatched_selector_args_bind,
            venomInstTheory.FIND_MEM]
QED
