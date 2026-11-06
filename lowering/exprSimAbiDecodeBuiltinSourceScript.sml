Theory exprSimAbiDecodeBuiltinSource
Ancestors
  exprSimAbiDecodeMemberExecute vyperABI vyperABIValid contractABI list

Theorem abi_decode_builtin_source_window:
  static_length (vyper_to_abi_type env ty) <= LENGTH bs /\
  LENGTH bs <= vyper_abi_size_bound env ty ==>
  (abi_decode_source_accepts env ty bs v <=>
   evaluate_abi_decode env ty bs = INL v)
Proof
  strip_tac >>
  simp[abi_decode_source_accepts_def, evaluate_abi_decode_def,
       vyper_valid_enc_window, decode_abi_value_def] >>
  Cases_on `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs` >> simp[] >>
  Cases_on `abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs)` >> simp[]
QED

Theorem abi_decode_builtin_source_size_reject:
  ~(static_length (vyper_to_abi_type env ty) <= LENGTH bs /\
    LENGTH bs <= vyper_abi_size_bound env ty) ==>
  evaluate_abi_decode env ty bs = INR "abi_decode invalid"
Proof
  simp[evaluate_abi_decode_def, vyper_valid_enc_window] >> metis_tac[]
QED

Theorem abi_decode_builtin_source_view_zero:
  (~is_dynamic (vyper_to_abi_type env ty) ==>
    LENGTH bs = static_length (vyper_to_abi_type env ty)) ==>
  abi_decode_source_view (vyper_to_abi_type env ty) bs 0 = bs
Proof
  simp[abi_decode_source_view_def] >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >> simp[] >>
  metis_tac[TAKE_LENGTH_ID]
QED

Theorem abi_decode_builtin_source_view_window:
  static_length (vyper_to_abi_type env ty) <= LENGTH bs /\
  LENGTH bs <= vyper_abi_size_bound env ty /\
  (~is_dynamic (vyper_to_abi_type env ty) ==>
    LENGTH bs = static_length (vyper_to_abi_type env ty)) ==>
  (abi_decode_source_accepts env ty
     (abi_decode_source_view (vyper_to_abi_type env ty) bs 0) v <=>
   evaluate_abi_decode env ty bs = INL v)
Proof
  strip_tac >> drule abi_decode_builtin_source_view_zero >>
  disch_then SUBST1_TAC >> irule abi_decode_builtin_source_window >> simp[]
QED

Theorem abi_decode_builtin_source_view_reject:
  static_length (vyper_to_abi_type env ty) <= LENGTH bs /\
  LENGTH bs <= vyper_abi_size_bound env ty /\
  (~is_dynamic (vyper_to_abi_type env ty) ==>
    LENGTH bs = static_length (vyper_to_abi_type env ty)) ==>
  ((~?v. abi_decode_source_accepts env ty
       (abi_decode_source_view (vyper_to_abi_type env ty) bs 0) v) <=>
   ?e. evaluate_abi_decode env ty bs = INR e)
Proof
  strip_tac >>
  `!v. abi_decode_source_accepts env ty
       (abi_decode_source_view (vyper_to_abi_type env ty) bs 0) v <=>
       evaluate_abi_decode env ty bs = INL v` by
    (gen_tac >> irule abi_decode_builtin_source_view_window >> simp[]) >>
  Cases_on `evaluate_abi_decode env ty bs` >> gvs[]
QED
