Theory bodyPtrPopGlobalLoweringInputs
Ancestors
  bodyPtrPopGlobalCompile compileVyper compileEnv vyperValue

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

(* Closed environment abbreviation for the diagnostic package.  Keeping it
   named avoids repeatedly normalizing higher-order type/selector fields. *)
Definition pop_global_package_env_def:
  pop_global_package_env =
    (build_compile_env pop_global_tops Internal Nonpayable "replace" []
      (BaseT (UintT 256)) pop_global_body F) with
      <| ce_is_ctor := F; ce_raw_return := F;
         ce_nonreentrant := (F,0,F,F) |>
End

Theorem pop_global_internal_label:
  internal_fn_label (build_func_ids 0 pop_global_tops "replace")
    "replace" [] F = "internal 0 replace()_runtime"
Proof
  EVAL_TAC
QED

Theorem pop_global_nkey:
  assign_nkeys pop_global_tops 0 "replace" = 0
Proof
  EVAL_TAC
QED

Theorem pop_global_internal_package:
  set_internal_package_target all_capabilities
    (package_internal_fn pop_global_tops F (assign_nkeys pop_global_tops 0) F 0
      (Nonpayable,F,F,"replace",[],([] : expr list),BaseT (UintT 256),pop_global_body)) =
    ("internal 0 replace()_runtime",pop_global_package_env,
     [],F,F,0,F,F,F,0,pop_global_body,SOME (BaseT (UintT 256)))
Proof
  simp[package_internal_fn_def, pop_global_internal_label, pop_global_nkey,
       pop_global_package_env_def, update_cenv_nonreentrant_def,
       returns_stack_count_def, compute_pass_via_stack_def] >> EVAL_TAC
QED
