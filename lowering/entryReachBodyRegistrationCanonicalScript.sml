(* Canonical call payload at any observation-preserving registration prefix. *)
Theory entryReachBodyRegistrationCanonical
Ancestors
  entryReachBodyPayloadBound entryReachBodyExactArrayLoop
  entryReachBodyCallInputs vyperLoweringCorrect vyperABI contractABI list words

Theorem entry_registration_canonical_payload:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  entry_loop_fields vs s ==>
  ?avs. LENGTH tx.args = LENGTH args /\
    vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
    LENGTH avs = LENGTH args /\
    mem_bytes_at 4
      (LENGTH (enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
        (ListV avs))) (abi_decode_source CALLDATALOAD s) =
      enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs) /\
    4 + LENGTH (enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args)))
      (ListV avs)) < dimword (:256)
Proof
  strip_tac >> drule_all entry_call_canonical_payload_bound >> strip_tac >>
  drule_all initial_venom_state_calldata_length >> strip_tac >>
  `s.vs_call_ctx = vs.vs_call_ctx` by fs[entry_loop_fields_def] >>
  qexists_tac `avs` >> simp[] >>
  irule (cj 1 entry_call_tuple_source) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`tx.function_name`, `vyper_to_abi_types (type_env tops) (MAP SND args)`] >>
  simp[]
QED
