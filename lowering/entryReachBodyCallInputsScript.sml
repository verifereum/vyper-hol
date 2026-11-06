Theory entryReachBodyCallInputs
Ancestors
  e2eDefs selectorDispatch vyperABIRoundtrip vyperABI vyperInterpreter
  vyperState list pair entryDispatchProps abiDecoderContract valueEncoding
  vyperLoweringCorrect words

(* Fix the selected source argument list before decomposing calldata; the
   transaction supplies every positional argument, so TAKE disappears. *)
Theorem entry_call_canonical_tuple:
  valid_vyper_call tops tx cd ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?avs.
    LENGTH tx.args = LENGTH args /\
    vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
    LENGTH avs = LENGTH args /\
    cd = function_selector tx.function_name
           (vyper_to_abi_types (type_env tops) (MAP SND args)) ++
         enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs)
Proof
  strip_tac >>
  gvs[valid_vyper_call_def, calldata_encodes_def, TAKE_LENGTH_TOO_LONG] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  gvs[]
QED

(* The canonical ABI payload starts just after the four selector bytes. *)
Theorem entry_call_tuple_source:
  s.vs_call_ctx.cc_calldata = function_selector name tys ++ bytes /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  mem_bytes_at 4 (LENGTH bytes) (abi_decode_source CALLDATALOAD s) = bytes /\
  4 + LENGTH bytes < dimword (:256)
Proof
  strip_tac >>
  `LENGTH (function_selector name tys) = 4` by
    simp[function_selector_length] >>
  `DROP 4 (function_selector name tys) = []` by
    metis_tac[DROP_LENGTH_NIL] >>
  conj_tac
  >- simp[abi_decode_source_def, mem_bytes_at_def, DROP_APPEND,
          rich_listTheory.TAKE_APPEND1] >>
  gvs[]
QED
