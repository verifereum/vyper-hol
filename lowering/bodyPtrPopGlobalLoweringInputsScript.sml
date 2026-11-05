Theory bodyPtrPopGlobalLoweringInputs
Ancestors
  bodyPtrPopGlobalCompile compileVyper vyperValue

Theorem pop_global_immutable_bound:
  compute_immutables_len
    (get_struct_fields (make_struct_fields_map pop_global_tops))
    pop_global_tops < 0x6000
Proof
  EVAL_TAC
QED

Theorem pop_global_allocs_ok:
  fn_allocs_ok pop_global_tops
    (Nonpayable,F,F,"replace",[],([] : expr list),BaseT (UintT 256),pop_global_body)
Proof
  simp[fn_allocs_ok_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_global_lowering_policy_ok:
  lowering_policy_ok pop_global_policy
Proof
  rewrite_tac[pop_global_policy_resolved] >> EVAL_TAC
QED
