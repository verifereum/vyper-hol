(* Conversion after acceptance of the capped, wrapped return encoding. *)
Theory abiReturnConversion
Ancestors
  abiVyperAdmissible abiWrappedDecodeProps vyperABI contractABI list

Theorem abi_returndata_admissible_success:
  let capped = TAKE (vyper_abi_size_bound env ty) bs in
  vyper_valid_enc_returndata env ty capped /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) capped) ==>
  ?v. evaluate_abi_decode_returndata env ty bs = INL v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_vyper_admissible_convert >> strip_tac >>
  simp[evaluate_abi_decode_returndata_def, decode_abi_value_def]
QED

Theorem abi_return_admissible_success:
  let rt = if needs_external_call_wrap ty then TupleT [ty] else ty in
  let capped = TAKE (vyper_abi_size_bound env rt) bs in
  vyper_valid_enc_returndata env rt capped /\
  abi_vyper_admissible env rt (dec (vyper_to_abi_type env rt) capped) ==>
  ?v. evaluate_abi_decode_return env ty bs = INL v
Proof
  simp_tac bool_ss [LET_THM] >>
  Cases_on `needs_external_call_wrap ty`
  >- (simp[] >> strip_tac >>
      qpat_x_assum `abi_vyper_admissible _ (TupleT _) _` mp_tac >>
      simp[Once abi_vyper_admissible_cases,
           abi_vyper_admissible_list_cons, abi_vyper_admissible_list_nil] >>
      strip_tac >> drule abi_vyper_admissible_convert >> strip_tac >>
      simp[evaluate_abi_decode_return_def, evaluate_abi_decode_returndata_def,
           decode_abi_value_def, abi_to_vyper_singleton_tuple]) >>
  simp[] >> strip_tac >>
  simp[evaluate_abi_decode_return_def] >>
  irule (SIMP_RULE bool_ss [LET_THM] abi_returndata_admissible_success) >> simp[]
QED
