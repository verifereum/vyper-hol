Theory entryAbiScalarTyping
Ancestors vyperTypeSystem vyperTyping vyperValue vyperABI contractABI words integer arithmetic

Theorem entry_base_abi_conversion_typed:
  evaluate_type tenv (BaseT bt) = SOME tv /\ value_has_type tv v /\
  abi_decode_bytes_widths tenv (BaseT bt) /\
  vyper_to_abi tenv (BaseT bt) v = SOME av ==>
  has_type (vyper_to_abi_type tenv (BaseT bt)) av
Proof
  Cases_on `bt` >> Cases_on `v` >>
  simp[evaluate_type_def, value_has_type_def, abi_decode_bytes_widths_def,
       vyper_to_abi_def, vyper_to_abi_base_def, vyper_to_abi_type_def,
       vyper_base_to_abi_type_def, has_type_def, valid_length_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_has_type_def, valid_int_bound_def, int_bits_bound_def,
      within_int_bound_def, dimword_def]
  >~ [`(if b then 1 else 0) < 2`] >- (Cases_on `b` >> simp[])
  >~ [`LENGTH l < 2 ** dimindex (:256)`] >- (fs[fcpLib.INDEX_CONV ``dimindex(:256)``])
  >~ [`w2n (word_of_bytes_be l) < _`]
  >- (mp_tac (wordsTheory.w2n_lt |> INST_TYPE [alpha |-> ``:160``]) >>
      simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  Cases_on `i < 0` >> gvs[PRE_SUB1] >>
  intLib.ARITH_TAC
QED

Theorem entry_flag_abi_conversion_typed:
  evaluate_type tenv (FlagT nsid) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi tenv (FlagT nsid) v = SOME av ==>
  has_type (vyper_to_abi_type tenv (FlagT nsid)) av
Proof
  Cases_on `v` >>
  simp[evaluate_type_def, vyper_to_abi_def, vyper_to_abi_type_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_has_type_def, has_type_def, valid_int_bound_def,
      int_bits_bound_def] >>
  `2 ** m <= 2 ** 256` by simp[EXP_BASE_LE_MONO] >>
  qpat_x_assum `2 ** m <= _`
    (mp_tac o CONV_RULE (RAND_CONV computeLib.EVAL_CONV)) >>
  decide_tac
QED
