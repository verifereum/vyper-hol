(* Source-success observations for raw, size-capped returndata. *)
Theory abiReturndataSource
Ancestors
  vyperABI contractABI list

Theorem abi_returndata_source_observation:
  evaluate_abi_decode_returndata env ty data = INL v ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (TAKE (vyper_abi_size_bound env ty) data) /\
  static_length (vyper_to_abi_type env ty) <=
    LENGTH (TAKE (vyper_abi_size_bound env ty) data) /\
  decode_abi_value env ty (TAKE (vyper_abi_size_bound env ty) data) = INL v
Proof
  simp[evaluate_abi_decode_returndata_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  gvs[vyper_valid_enc_returndata_def]
QED

Theorem abi_return_source_observation:
  evaluate_abi_decode_return env ty data = INL v ==>
  evaluate_abi_decode_returndata env
    (if needs_external_call_wrap ty then TupleT [ty] else ty) data =
    INL (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v)
Proof
  simp[evaluate_abi_decode_return_def] >>
  Cases_on `needs_external_call_wrap ty` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED
