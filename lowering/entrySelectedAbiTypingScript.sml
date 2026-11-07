Theory entrySelectedAbiTyping
Ancestors
  entryAbiForwardTyping entrySelectedAbiWidths entrySelectedSourceCardinality
  entrySelectedEncodingBounds entryDecodeProps vyperABIRoundtrip vyperTypeABI vyperABI
  vyperTypeSystem vyperTyping vyperInterpreter vyperLoweringCorrect e2eDefs
  selectorDispatch contractABI valueEncodingProofs list rich_list words

Theorem source_list_conversion_typed[local]:
  LIST_REL (\ty v. assignable_type env ty /\
    ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vals /\
  EVERY (abi_decode_bytes_widths env) tys /\
  EVERY entry_tuple_cardinality (vyper_to_abi_types env tys) /\
  vyper_to_abi_list env tys vals = SOME avs ==>
  has_types (vyper_to_abi_types env tys) avs
Proof
  strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >>
  gvs[has_types_LIST_REL, LIST_REL_EL_EQN, EVERY_EL,
      vyper_to_abi_types_length, vyper_to_abi_types_EL] >>
  rpt strip_tac >> irule entry_assignable_abi_conversion_typed >>
  metis_tac[]
QED

Theorem selected_call_abi_values_typed:
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env ==>
  ?avs.
    vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
    has_types (vyper_to_abi_types (type_env tops) (MAP SND args)) avs /\
    vs.vs_call_ctx.cc_calldata =
      function_selector tx.function_name
        (vyper_to_abi_types (type_env tops) (MAP SND args)) ++
      enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
        (ListV avs) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
      (ListV avs)) < dimword (:256)
Proof
  strip_tac >> drule_all selected_call_encoding_cap >> strip_tac >>
  drule_all selected_call_source_values >> strip_tac >>
  drule_all selected_call_parameter_tuple_cardinality >> strip_tac >>
  drule_all selected_external_parameter_abi_widths >> strip_tac >>
  qexists `avs` >> simp[] >> irule source_list_conversion_typed >>
  goal_assum (drule_at Any) >> simp[] >> qexists `tx.args` >> simp[]
QED
