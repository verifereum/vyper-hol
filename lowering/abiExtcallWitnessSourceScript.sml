(* Source evaluation with an arbitrary gas-observation suffix. *)
Theory abiExtcallWitnessSource
Ancestors
  abiExtcallWitnessRecords abiExtcallWitnessProbe abiExtcallWrapReachProbe
  vyperInterpreter vyperABI vyperState vyperValue vyperContext
  vyperEvmBoundary exprSimDefs gasContext byte cv_std valueEncodingProofs
  vyperCallOutcome extCallOracle

Definition witness_end_def:
  witness_end = SND (eval_expr witness_cx witness_expr witness_es)
End

Theorem witness_target_evals:
  eval_exprs witness_cx [witness_target] s =
    (INL [BytesV (REPLICATE 18 0w ++ [1w;0w])], s)
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_gas_evals:
  eval_exprs witness_cx [witness_gas] s = (INL [IntV 10000], s)
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_source_stages:
  eval_expr witness_cx witness_expr s =
    eval_ext_call witness_cx T T ("probe",[],reach_return) [EKGas]
      [BytesV (REPLICATE 18 0w ++ [1w;0w]); IntV 10000] s
Proof
  `eval_exprs witness_cx [witness_target] =
     (\s. (INL [BytesV (REPLICATE 18 0w ++ [1w;0w])],s))` by
    simp[FUN_EQ_THM, witness_target_evals] >>
  `eval_exprs witness_cx [witness_gas] =
     (\s. (INL [IntV 10000],s))` by
    simp[FUN_EQ_THM, witness_gas_evals] >>
  rewrite_tac[witness_expr_def] >> once_rewrite_tac[evaluate_def] >>
  asm_rewrite_tac[] >>
  simp[Once evaluate_def, bind_def, return_def, read_results_def]
QED

Theorem witness_calldata_exists:
  IS_SOME (build_ext_calldata FEMPTY "probe" [] [])
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_address_decode:
  word_of_bytes_be (REPLICATE 18 0w ++ [1w;0w]) = (256w:address)
Proof
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss)
    [word_of_bytes_be_eq_num_of_bytes, dividesTheory.compute_divides] >>
  EVAL_TAC >> simp[]
QED

Theorem witness_call_boundary:
  eval_ext_call witness_cx T T ("probe",[],reach_return) [EKGas]
    [BytesV (REPLICATE 18 0w ++ [1w;0w]); IntV 10000] s =
  bind (eval_ext_call_effects witness_cx 256w
    (THE (build_ext_calldata FEMPTY "probe" [] [])) NONE
    10000 s.accounts)
    (\bs. bind (lift_sum_runtime (evaluate_abi_decode_return FEMPTY reach_return bs))
      (\v. return (Value v))) s
Proof
  simp[eval_ext_call_def, ext_call_opts_ok_def, ext_call_kwarg_def,
       ext_call_precheck_ok_def, reach_return_def, witness_tenv,
       frame_call_value_def, forwarded_gas_def, dest_AddressV_def] >>
  simp[type_check_def, check_def, lift_option_type_def, bind_def,
       ignore_bind_def, return_def, get_accounts_def, dest_NumV_def,
       witness_cx_def] >>
  simp[assert_def, empty_call_txn_def, default_evm_gas_limit_def,
       witness_address_decode] >>
  mp_tac witness_calldata_exists >>
  Cases_on `build_ext_calldata FEMPTY "probe" [] []` >> simp[return_def]
QED

Theorem witness_effects:
  eval_ext_call_effects witness_cx 256w data NONE gas accounts
    (witness_es with gas_obs := gs) =
  (INL reach_bytes, witness_es with
    <|gas_obs := gs; outcomes := SOME [];
      requests := [call_outcome_request 256w data NONE witness_es]|>)
Proof
  simp[eval_ext_call_effects_def, bind_def, return_def, ignore_bind_def,
       take_call_outcome_def, adopt_call_outcome_def,
       witness_es_def, take_outcome_def, record_request_def,
       call_outcome_request_def, adopt_outcome_def, adopt_outcome_deletions_def] >>
  simp[computed_precompile_def, precompile_result_def, reach_outcome_def, bind_def, return_def,
       adopt_call_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def,
       empty_state_def]
QED

Theorem witness_source_explicit:
  eval_expr witness_cx witness_expr (witness_es with gas_obs := gs) =
    (INR (Error (RuntimeError "abi_decode invalid")), witness_es with
      <|gas_obs := gs; outcomes := SOME [];
        requests := [call_outcome_request 256w
          (THE (build_ext_calldata FEMPTY "probe" [] [])) NONE witness_es]|>)
Proof
  rewrite_tac[witness_source_stages, witness_call_boundary, bind_def] >>
  rewrite_tac[witness_effects] >>
  simp[reach_source_rejects, lift_sum_runtime_def, raise_def, bind_def]
QED

Theorem witness_end_explicit:
  witness_end = witness_es with
    <|outcomes := SOME [];
      requests := [call_outcome_request 256w
        (THE (build_ext_calldata FEMPTY "probe" [] [])) NONE witness_es]|>
Proof
  mp_tac (Q.INST [`gs` |-> `[]`] witness_source_explicit) >>
  simp[witness_end_def, witness_es_def, empty_state_def]
QED

Theorem witness_source_run:
  !gs. eval_expr witness_cx witness_expr (witness_es with gas_obs := gs) =
    (INR (Error (RuntimeError "abi_decode invalid")), witness_end with gas_obs := gs)
Proof
  simp[witness_source_explicit, witness_end_explicit]
QED

Theorem witness_source_admissible:
  gas_admissible (eval_expr witness_cx witness_expr) expr_vv_res_ok witness_es
Proof
  simp[gas_admissible_def, witness_source_run, expr_vv_res_ok_def]
QED
