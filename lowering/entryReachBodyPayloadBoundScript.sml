Theory entryReachBodyPayloadBound
Ancestors
  entryReachBodyCallInputs vyperLoweringCorrect e2eDefs selectorDispatch
  vyperInterpreter vyperABI contractABI list words entryDispatchProps

Theorem entry_call_canonical_payload_bound:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?avs. LENGTH tx.args = LENGTH args /\
    vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
    LENGTH avs = LENGTH args /\
    vs.vs_call_ctx.cc_calldata = function_selector tx.function_name
      (vyper_to_abi_types (type_env tops) (MAP SND args)) ++
      enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs) /\
    4 + LENGTH (enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
      (ListV avs)) < dimword (:256)
Proof
  strip_tac >>
  drule_all initial_venom_state_calldata_length >> strip_tac >>
  drule_all entry_call_canonical_tuple >> strip_tac >>
  qexists_tac `avs` >> gvs[function_selector_length]
QED
