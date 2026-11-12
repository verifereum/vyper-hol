Theory entrySelectedSourceCardinality
Ancestors
  entrySelectedEncodingBounds entryParameterAdmissibility entryArgumentCastFacts
  entryHereditarySlotCardinality vyperLoweringCorrect e2eDefs supportedProgram
  vyperInterpreter vyperTyping vyperTypeABI vyperABI list rich_list pair

Theorem selected_call_source_values:
  supported_program tops /\ source_typing_ok tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env ==>
  LIST_REL (\ty v. assignable_type (type_env tops) ty /\
    ?tv. evaluate_type (type_env tops) ty = SOME tv /\ value_has_type tv v)
    (MAP SND args) tx.args
Proof
  strip_tac >> drule bind_arguments_source_values >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac
  >- (`MEM (FST (EL n args), SND (EL n args)) args` by
        (simp[] >> irule EL_MEM >> simp[]) >>
      drule_all selected_external_parameter_assignable >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[] >> Cases_on `EL n args` >> simp[] >> metis_tac[]
QED

Theorem selected_call_parameter_tuple_cardinality:
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env ==>
  EVERY entry_tuple_cardinality
    (vyper_to_abi_types (type_env tops) (MAP SND args))
Proof
  strip_tac >> drule_all selected_call_source_values >> strip_tac >>
  drule_all selected_call_encoding_cap >> strip_tac >>
  drule_all source_list_encoding_tuple_cardinality >> simp[]
QED
