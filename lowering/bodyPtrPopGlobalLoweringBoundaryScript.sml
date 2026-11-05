Theory bodyPtrPopGlobalLoweringBoundary
Ancestors
  bodyPtrPopGlobalLoweringInputs bodyPtrPopGlobalCompile compileVyper
  vyperCompiler compileEnv moduleLowering

(* Closed package list shared by the generation and extraction boundaries. *)
Definition pop_global_packages_def:
  pop_global_packages =
    [("internal 0 replace()_runtime",pop_global_package_env,
      [] : (string # bool) list,F,F,0,F,F,F,0,pop_global_body,
      SOME (BaseT (UintT 256)))]
End

Theorem pop_global_lowering_run:
  lower_vyper_runtime_unit pop_global_tops pop_global_policy =
  run_lowering [] [] pop_global_packages NONE pop_global_policy 0 0
    ([] : dense_bucket list) (K ("",0,F)) "__entry"
Proof
  rewrite_tac[pop_global_lowering_frontend] >>
  simp[pop_global_immutable_bound, pop_global_allocs_ok,
       pop_global_internal_package, pop_global_packages_def,
       package_fallback_fn_def, set_fallback_package_target_def,
       build_dense_entry_info_def, pop_global_policy_resolved]
QED

Theorem pop_global_lowering_boundary:
  lower_vyper_runtime_unit pop_global_tops pop_global_policy =
  case extract_context_with_internals "__entry" pop_global_packages
    (SND (compile_generate_runtime [] [] pop_global_packages NONE Linear
      0 0 ([] : dense_bucket list) (K ("",0,F))
      (initial_compile_state "__entry"))) of
    NONE => NONE
  | SOME (ctx,data) =>
      if lowering_context_ok ctx then
        SOME <| cu_context := ctx; cu_data_segment := data |>
      else NONE
Proof
  rewrite_tac[pop_global_lowering_run, run_lowering_def,
              pop_global_lowering_policy_ok] >>
  simp[pop_global_policy_resolved] >> pairarg_tac >> simp[]
QED

Theorem pop_global_initial_fresh_label:
  fresh_label "fallback" (initial_compile_state "__entry") =
    ("@fallback_0",
     (initial_compile_state "__entry") with cs_next_label := 1)
Proof
  simp[fresh_label_def, initial_compile_state_def] >> EVAL_TAC
QED
