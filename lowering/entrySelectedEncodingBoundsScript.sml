Theory entrySelectedEncodingBounds
Ancestors
  entryHereditaryEncodingCardinality entryEncodingCardinality
  entryDecodeProps vyperABI vyperABIRoundtrip vyperTypeABI vyperTyping vyperTypeSystem
  vyperLoweringCorrect e2eDefs selectorDispatch contractABI
  valueEncodingProofs list rich_list words

Theorem selected_call_encoding_cap:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?avs.
    vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
    vs.vs_call_ctx.cc_calldata =
      function_selector tx.function_name
        (vyper_to_abi_types (type_env tops) (MAP SND args)) ++
      enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
        (ListV avs) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
      (ListV avs)) < dimword (:256)
Proof
  strip_tac >> drule_all initial_venom_state_calldata_length >> strip_tac >>
  gvs[valid_vyper_call_def, calldata_encodes_def, Excl "enc_def"] >>
  `TAKE (LENGTH args) (MAP SND args) = MAP SND args` by
    (irule TAKE_LENGTH_TOO_LONG >> simp[]) >>
  qexists `abi_vals` >>
  gvs[LENGTH_APPEND, Excl "enc_def"] >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem source_list_encoding_tuple_cardinality:
  LIST_REL (\ty v. assignable_type env ty /\
    ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vals /\
  vyper_to_abi_list env tys vals = SOME avs /\
  LENGTH (enc (Tuple (vyper_to_abi_types env tys)) (ListV avs)) <
    dimword (:256) ==>
  EVERY entry_tuple_cardinality (vyper_to_abi_types env tys)
Proof
  strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >>
  gvs[EVERY_EL, LIST_REL_EL_EQN, vyper_to_abi_types_length,
      vyper_to_abi_types_EL, Excl "enc_def"] >> rpt strip_tac >>
  `LENGTH (enc (EL n (vyper_to_abi_types env tys)) (EL n avs)) <=
     LENGTH (enc (Tuple (vyper_to_abi_types env tys)) (ListV avs))` by
    (irule tuple_encoding_member_bound >> simp[vyper_to_abi_types_length]) >>
  `LENGTH (enc (vyper_to_abi_type env (EL n tys)) (EL n avs)) <
     dimword (:256)` by (gvs[vyper_to_abi_types_EL, Excl "enc_def"]) >>
  irule source_encoding_tuple_cardinality >>
  metis_tac[]
QED
