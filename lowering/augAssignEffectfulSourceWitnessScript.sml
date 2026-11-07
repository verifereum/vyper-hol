(* Concrete source-only witness; no compiler or invariant admission claim. *)
Theory augAssignEffectfulSourceWitness
Ancestors
  augAssignEffectfulContinuationProbe augAssignEffectfulContractProbe
  vyperInterpreter vyperState vyperContext vyperCallOutcome vyperABI vfmState finite_map

Definition effaug_array_ty_def:
  effaug_array_ty = ArrayT (ArrayT (BaseT (UintT 8)) (Fixed 1)) (Dynamic 1)
End

Definition effaug_tops_def:
  effaug_tops = [VariableDecl Private Storage "a" effaug_array_ty (SOME 0)]
End

Definition effaug_cx_def:
  effaug_cx = empty_evaluation_context with
    <|sources := [(0w, [(NONE, effaug_tops)])];
      layouts := [(0w, ([((NONE,"a"),0)], []))]|>
End

Definition effaug_accounts_def:
  effaug_accounts payload =
    (20w =+ (empty_account_state with code := [0w]))
      ((0w =+ (empty_account_state with storage := payload)) empty_accounts)
End

Definition effaug_outcome_def:
  effaug_outcome =
    <|co_created := 0w; co_toDelete := []; co_success := T;
      co_returnData := REPLICATE 32 0w;
      co_accounts := effaug_accounts (update_storage 1w 256w (\k. 0w));
      co_tStorage := empty_transient_storage; co_logs := []|>
End

Definition effaug_es_def:
  effaug_es = empty_state with
    <|accounts := effaug_accounts (update_storage 0w 1w (\k. 0w));
      outcomes := SOME [effaug_outcome]|>
End

Definition effaug_index_def:
  effaug_index = Call (BaseT (UintT 256))
    (ExtCall F F ("f", [], BaseT (UintT 256)) [])
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [20w]))] NONE
End

Definition effaug_stmt_def:
  effaug_stmt = AugAssign (BaseT (UintT 8))
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
        (Literal (BaseT (UintT 256)) (IntL 0))) effaug_index)
    Add (Literal (BaseT (UintT 8)) (IntL 1))
End

Theorem effaug_abi_zero:
  evaluate_abi_decode_return FEMPTY (BaseT (UintT 256)) (REPLICATE 32 0w) =
    INL (IntV 0)
Proof
  EVAL_TAC >> simp[]
QED

Theorem effaug_global_place:
  eval_base_place effaug_cx (TopLevelNameTarget (NONE,"a"))
    (effaug_es with gas_obs := obs) =
    (INL (PlaceR (StoragePlace F 0w
      (ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1)))),
     effaug_es with gas_obs := obs)
Proof
  simp[Once evaluate_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``effaug_es``]) >>
  simp[vyperValueTheory.type_slot_size_def, SF wordsLib.SIZES_ss,
       return_def]
QED

Theorem effaug_outer_place:
  eval_base_place effaug_cx
    (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    (effaug_es with gas_obs := obs) =
    (INL (PlaceR (StoragePlace F 1w
      (ArrayTV (BaseTV (UintT 8)) (Fixed 1)))),
     effaug_es with gas_obs := obs)
Proof
  pure_once_rewrite_tac[evaluate_def] >>
  simp[effaug_global_place, bind_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``effaug_es``, ``effaug_cx``]) >>
  simp[effaug_es_def, effaug_cx_def, effaug_accounts_def,
       empty_evaluation_context_def, empty_state_def, update_storage_def,
       return_def] >> EVAL_TAC
QED


Theorem effaug_calldata:
  build_ext_calldata env "f" [] [] =
    SOME (function_selector "f" [] ++ enc (Tuple []) (ListV []))
Proof
  simp[build_ext_calldata_def, vyper_to_abi_type_def, vyper_to_abi_def]
QED

Theorem effaug_address:
  dest_AddressV (BytesV (REPLICATE 19 0w ++ [20w])) = SOME 20w
Proof
  EVAL_TAC >>
  rewrite_tac[byteTheory.set_byte_bit_field_insert] >>
  simp[byteTheory.byte_index_def, SF wordsLib.SIZES_ss] >>
  CONV_TAC wordsLib.WORD_EVAL_CONV
QED

Theorem effaug_accounts_typed:
  accounts_runtime_well_typed (effaug_accounts payload)
Proof
  simp[vyperRuntimeAccountsTheory.accounts_runtime_well_typed_def,
       vyperRuntimeAccountsTheory.account_runtime_well_typed_def,
       effaug_accounts_def, lookup_account_def, empty_accounts_def,
       empty_account_state_def, combinTheory.APPLY_UPDATE_THM] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[empty_storage_def]
QED

Theorem effaug_effects:
  eval_ext_call_effects effaug_cx 20w calldata (SOME 0) gas accounts
    (effaug_es with gas_obs := obs) =
    (INL (REPLICATE 32 0w),
     effaug_es with <|gas_obs := obs; outcomes := SOME [];
       requests := [call_outcome_request 20w calldata (SOME 0) effaug_es];
       accounts := effaug_outcome.co_accounts;
       tStorage := effaug_outcome.co_tStorage; logs := []|>)
Proof
  simp[eval_ext_call_effects_def, bind_def, return_def, effaug_es_def,
       empty_state_def] >>
  simp[take_call_outcome_def, call_outcome_request_def,
       extCallOracleTheory.take_outcome_def, extCallOracleTheory.record_request_def,
       extCallOracleTheory.computed_precompile_def] >>
  simp[extCallOracleTheory.precompile_result_ordinary,
       effaug_outcome_def, effaug_accounts_typed,
       adopt_call_outcome_equation, ignore_bind_def, bind_def, return_def]
QED

Theorem effaug_index_run:
  eval_expr effaug_cx effaug_index (effaug_es with gas_obs := obs) =
    (INL (Value (IntV 0)),
     effaug_es with <|gas_obs := obs; outcomes := SOME [];
       requests := [call_outcome_request 20w
         (function_selector "f" [] ++ enc (Tuple []) (ListV [])) (SOME 0) effaug_es];
       accounts := effaug_outcome.co_accounts;
       tStorage := effaug_outcome.co_tStorage; logs := []|>)
Proof
  simp[effaug_index_def, Once evaluate_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``effaug_es``, ``effaug_cx``,
    ``effaug_outcome``, ``eval_ext_call``, ``function_selector``, ``enc``, ``REPLICATE``]) >>
  simp[eval_ext_call_def, effaug_address, ext_call_opts_ok_def,
       ext_call_kwarg_def, effaug_calldata] >>
  simp[type_check_def, assert_def, lift_option_type_def,
       bind_def, ignore_bind_def, return_def, get_accounts_def,
       ext_call_precheck_ok_def, check_def] >>
  `~effaug_cx.txn.is_static /\ get_tenv effaug_cx = FEMPTY` by
    (EVAL_TAC >> simp[]) >>
  simp[frame_call_value_def, return_def, effaug_effects, effaug_abi_zero,
       lift_sum_runtime_def, call_outcome_request_def, listTheory.REV_DEF]
QED

Definition effaug_post_def:
  effaug_post obs =
     effaug_es with <|gas_obs := obs; outcomes := SOME [];
       requests := [call_outcome_request 20w
         (function_selector "f" [] ++ enc (Tuple []) (ListV [])) (SOME 0) effaug_es];
       accounts := effaug_outcome.co_accounts;
       tStorage := effaug_outcome.co_tStorage; logs := []|>
End

Theorem effaug_target_run:
  eval_target_place effaug_cx
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
        (Literal (BaseT (UintT 256)) (IntL 0))) effaug_index)
    (effaug_es with gas_obs := obs) =
    (INL (StoragePlace F 1w (BaseTV (UintT 8))), effaug_post obs)
Proof
  irule saved_fixed_index_after_effect >>
  simp[effaug_outer_place, effaug_index_run, effaug_post_def]
QED

Theorem effaug_post_storage:
  get_storage effaug_cx (effaug_post obs) F = update_storage 1w 256w (\k. 0w)
Proof
  simp[effaug_post_def, effaug_outcome_def, vyperStorageBackendTheory.get_storage_def,
       effaug_cx_def, empty_evaluation_context_def,
       effaug_accounts_def, lookup_account_def, empty_call_txn_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem effaug_source_run:
  eval_stmt effaug_cx effaug_stmt (effaug_es with gas_obs := obs) =
    (INL (), (effaug_post obs) with accounts :=
      effaug_accounts (update_storage 1w 1w (\k. 0w)))
Proof
  pure_rewrite_tac[effaug_stmt_def] >>
  pure_once_rewrite_tac[evaluate_def] >>
  simp[effaug_target_run, bind_def, ignore_bind_def,
       saved_scalar_read_noncanonical, effaug_post_storage,
       saved_scalar_type_after_effect] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``effaug_cx``, ``effaug_post``,
    ``write_place``]) >>
  simp[return_def, write_place_def, write_storage_slot_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``effaug_cx``, ``effaug_post``,
    ``get_storage_backend``, ``set_storage_backend``]) >>
  `~effaug_cx.txn.is_static` by EVAL_TAC >>
  simp[get_storage_backend_def, set_storage_backend_def,
       get_accounts_def, bind_def, return_def, update_accounts_def] >>
  simp[effaug_post_def, effaug_outcome_def, effaug_accounts_def,
       effaug_cx_def, empty_evaluation_context_def, empty_call_txn_def,
       lookup_account_def, update_account_def, update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  simp[evaluation_state_component_equality, FUN_EQ_THM,
       combinTheory.APPLY_UPDATE_THM, empty_account_state_def] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[empty_storage_def]
QED

Theorem effaug_source_success:
  !obs. FST (eval_stmt effaug_cx effaug_stmt (effaug_es with gas_obs := obs)) = INL ()
Proof
  simp[effaug_source_run]
QED

Theorem effaug_source_final_storage:
  get_storage effaug_cx
    (SND (eval_stmt effaug_cx effaug_stmt (effaug_es with gas_obs := obs))) F =
    update_storage 1w 1w (\k. 0w)
Proof
  simp[effaug_source_run, vyperStorageBackendTheory.get_storage_def,
       effaug_accounts_def, effaug_cx_def, empty_evaluation_context_def,
       empty_call_txn_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem effaug_no_gas_exempt_cert:
  ~gas_exempt_cert memory tops (ctx,func)
    (eval_stmt effaug_cx effaug_stmt) (effaug_es,s0)
    marks (err,ee) (leaf,finish_state)
Proof
  irule source_replay_excludes_gas_exempt_cert >>
  simp[effaug_source_run]
QED
