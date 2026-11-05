Theory bodyPtrPopGlobalCompile
Ancestors
  bodyPtrPopGlobalLegality compileVyper venomCompilerTypes alist integer_word
Libs finite_mapLib computeLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])

(* Closed resolved policy for the diagnostic whole-unit lowering probe. *)
Definition pop_global_policy_def:
  pop_global_policy = THE (resolve_o1_policy (o1_policy all_capabilities))
End

Theorem pop_global_classification:
  classify_functions pop_global_tops =
    ([], [(Nonpayable,F,F,"replace",[],[],BaseT (UintT 256),pop_global_body)],
     NONE, NONE)
Proof
  simp[pop_global_tops_def, classify_functions_def, classify_function_def]
QED

Theorem pop_global_selectors:
  build_selectors (type_env pop_global_tops) [] = []
Proof
  simp[build_selectors_def]
QED

Theorem pop_global_external_packages:
  MAP (set_external_package_target pop_global_policy.rpol_target o
       package_external_fn pop_global_tops F (assign_nkeys pop_global_tops 0))
    [] = []
Proof
  simp[]
QED

Theorem pop_global_policy_resolved:
  pop_global_policy = <| rpol_target := all_capabilities;
    rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize |>
Proof
  EVAL_TAC
QED

(* Frontend cut only: the internal package and allocation guard remain opaque. *)
Theorem pop_global_lowering_frontend:
  lower_vyper_runtime_unit pop_global_tops pop_global_policy =
    if compute_immutables_len
         (get_struct_fields (make_struct_fields_map pop_global_tops))
         pop_global_tops < 0x6000 /\
       fn_allocs_ok pop_global_tops
         (Nonpayable,F,F,"replace",[],[],BaseT (UintT 256),pop_global_body)
    then
      run_lowering [] []
        [set_internal_package_target all_capabilities
          (package_internal_fn pop_global_tops F
            (assign_nkeys pop_global_tops 0) F 0
            (Nonpayable,F,F,"replace",[],([] : expr list),BaseT (UintT 256),pop_global_body))]
        (set_fallback_package_target all_capabilities
          (package_fallback_fn pop_global_tops F
            (assign_nkeys pop_global_tops 0) NONE))
        pop_global_policy 0 0 ([] : dense_bucket list)
        (build_dense_entry_info [] []) "__entry"
    else NONE
Proof
  simp[Once lower_vyper_runtime_unit_def, pop_global_classification,
       pop_global_selectors, pop_global_policy_resolved,
       package_fallback_fn_def, set_fallback_package_target_def,
       build_dense_entry_info_def]
QED
