(* The successful plain nonreentrant dispatch delivers the post-binding endpoint. *)
Theory s1PrefixRegisteredEndpoint
Ancestors
  runtimeEntryEndpoint e2eDefs vyperLoweringCorrect vyperCalldata compileVyper
  exprSimHypsDefs constSubst supportedProgram ptrDiscipline contextRawReachable
Libs
  dispatchedRegisteredEndpointLib

Theorem dispatched_nonreentrant_endpoint:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name,tx.args) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) ==>
  runtime_body_endpoint tops rpolicy unit am tx vs es0 mut T args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  split_dispatch_tac
  >- (fallback_registration_tac >> fallback_endpoint_tac >> first_assum ACCEPT_TAC) >>
  selected_registration_tac >> selected_endpoint_tac >> first_assum ACCEPT_TAC
QED
