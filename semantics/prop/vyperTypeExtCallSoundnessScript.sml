(*
 * External-call and low-level call helper lemmas for Vyper statement soundness.
 *
 * This theory factors the extcall/raw-call/create/selfdestruct helper cluster out
 * of vyperTypeStmtSoundness so it can be built/debugged independently.
 *)

Theory vyperTypeExtCallSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperCreate vyperCreateFrame vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperRuntimeAccounts vyperCallFrame
  vyperTypeExtCallCore[ignore_grammar] vyperTypeCallOutcome[ignore_grammar] vyperCallOutcomeProps[ignore_grammar]
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeArgFits
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
Libs
  wordsLib markerLib intLib BasicProvers

val _ = Parse.hide "from"

Theorem transfer_value_zero[simp]:
  transfer_value from to 0 st = (INL (), st)
Proof
  simp[transfer_value_def, return_def]
QED

Theorem transfer_value_same_address[simp]:
  transfer_value addr addr amount st = (INL (), st)
Proof
  simp[transfer_value_def, return_def]
QED

Theorem transfer_value_recipient_overflow_regression:
  let from = (0w:address) in
  let to = (1w:address) in
  let sender = empty_account_state with balance := 1 in
  let recipient = empty_account_state with balance := 2 ** 256 - 1 in
  let st = empty_state with accounts :=
             update_account from sender (update_account to recipient empty_accounts) in
    accounts_well_typed st.accounts /\
    FST (transfer_value from to 1 st) <> INL () /\
    accounts_well_typed (SND (transfer_value from to 1 st)).accounts
Proof
  EVAL_TAC >> gen_tac >>
  Cases_on `addr = 0w` >> gvs[] >>
  Cases_on `addr = 1w` >> gvs[]
QED

Theorem make_ext_call_state_value_transfer_can_break_accounts_well_typed:
  let caller = (0w:address) in
  let callee = (1w:address) in
  let caller_acct = empty_account_state with balance := 1 in
  let callee_acct = empty_account_state with balance := 2 ** 256 - 1 in
  let accounts = update_account caller caller_acct
                   (update_account callee callee_acct empty_accounts) in
  let st0 = make_ext_call_state caller callee [] [] (SOME 1) default_evm_gas_limit
              accounts empty_transient_storage (vyper_to_tx_params empty_call_txn) in
    accounts_well_typed accounts /\
    ~accounts_well_typed st0.rollback.accounts
Proof
  EVAL_TAC >> conj_tac
  >- (gen_tac >>
      Cases_on `addr = 0w` >> gvs[] >>
      Cases_on `addr = 1w` >> gvs[]) >>
  strip_tac >>
  first_x_assum (qspec_then `1w:address` mp_tac) >> EVAL_TAC
QED
Theorem extract_call_result_success_exposes_bad_accounts:
  let caller = (0w:address) in
  let callee = (1w:address) in
  let caller_acct = empty_account_state with balance := 1 in
  let callee_acct = empty_account_state with balance := 2 ** 256 - 1 in
  let good_accounts = update_account caller caller_acct
                        (update_account callee callee_acct empty_accounts) in
  let bad_accounts = (make_ext_call_state caller callee [] [] (SOME 1) default_evm_gas_limit
                        good_accounts empty_transient_storage
                        (vyper_to_tx_params empty_call_txn)).rollback.accounts in
  let final_state = (make_ext_call_state caller callee [] [] (SOME 1) default_evm_gas_limit
                       good_accounts empty_transient_storage
                       (vyper_to_tx_params empty_call_txn)) with
                      rollback updated_by (\rb. rb with accounts := bad_accounts) in
    accounts_well_typed good_accounts /\
    ~accounts_well_typed bad_accounts /\
    ?retData tStorage' emitted_logs.
      extract_call_result good_accounts empty_transient_storage
        (INR NONE, final_state) =
        SOME (T, retData, bad_accounts, tStorage', emitted_logs)
Proof
  EVAL_TAC >> conj_tac
  >- (gen_tac >>
      Cases_on `addr = 0w` >> gvs[] >>
      Cases_on `addr = 1w` >> gvs[]) >>
  conj_tac
  >- (strip_tac >>
      first_x_assum (qspec_then `1w:address` mp_tac) >> EVAL_TAC) >>
  qexists_tac `[]` >>
  qexists_tac `empty_transient_storage` >>
  qexists_tac `[]` >>
  EVAL_TAC
QED

Theorem run_ext_call_overflowing_value_transfer_rejected:
  let caller = (0w:address) in
  let callee = (1w:address) in
  let caller_acct = empty_account_state with balance := 1 in
  let callee_acct = empty_account_state with balance := 2 ** 256 - 1 in
  let accounts = update_account caller caller_acct
                   (update_account callee callee_acct empty_accounts) in
    run_ext_call caller callee [] (SOME 1) default_evm_gas_limit
      accounts empty_transient_storage
      (vyper_to_tx_params empty_call_txn) = NONE
Proof
  EVAL_TAC
QED

(* TASK032: original proof moved unchanged below the oracle integration. *)
Theorem accounts_runtime_well_typed_accounts_well_typed:
  !acc. accounts_runtime_well_typed acc <=> accounts_well_typed acc
Proof
  ACCEPT_TAC vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed
QED

Theorem ext_call_success_accounts_ok_imp_extract_premise:
  !outcome.
    ext_call_success_accounts_ok outcome ==>
    (case FST outcome of
     | INR NONE => accounts_well_typed (SND outcome).rollback.accounts
     | _ => T)
Proof
  Cases >> rename1 `(result, final_state)` >>
  Cases_on `result` >>
  simp[ext_call_success_accounts_ok_def, ext_call_success_accounts_ok_aux_def,
       accounts_runtime_well_typed_accounts_well_typed] >>
  Cases_on `y` >> simp[]
QED

Theorem extract_call_result_accounts_well_typed:
  !orig_accounts orig_tStorage result final_state
   success retData accounts' tStorage' emitted_logs.
    accounts_well_typed orig_accounts /\
    (case result of
     | INR NONE => accounts_well_typed final_state.rollback.accounts
     | _ => T) /\
    extract_call_result orig_accounts orig_tStorage (result, final_state) =
      SOME (success, retData, accounts', tStorage', emitted_logs) ==>
    accounts_well_typed accounts'
Proof
  rw[extract_call_result_def] >>
  gvs[AllCaseEqs()]
QED

Theorem run_ext_call_accounts_well_typed:
  !caller callee calldata value_opt gas accounts tStorage txParams
   success retData accounts' tStorage' emitted_logs.
    accounts_well_typed accounts /\
    run_ext_call caller callee calldata value_opt gas accounts tStorage txParams =
      SOME (success, retData, accounts', tStorage', emitted_logs) ==>
    accounts_well_typed accounts'
Proof
  rw[run_ext_call_def] >>
  gvs[AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `extract_call_result _ _ outcome = SOME _` >>
  PairCases_on `outcome` >>
  drule ext_call_success_accounts_ok_imp_extract_premise >>
  strip_tac >>
  qspecl_then [`accounts`, `tStorage`, `outcome0`, `outcome1`,
               `success`, `retData`, `accounts'`, `tStorage'`]
    mp_tac extract_call_result_accounts_well_typed >>
  simp[] >>
  gvs[]
QED

Theorem run_delegate_call_accounts_well_typed:
  accounts_well_typed accounts /\
  run_delegate_call cx target_addr calldata accounts tStorage =
    SOME (success,retData,accounts',tStorage',emitted_logs) ==>
  accounts_well_typed accounts'
Proof
  rw[run_delegate_call_def] >> gvs[AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `extract_call_result _ _ outcome = SOME _` >>
  PairCases_on `outcome` >>
  drule ext_call_success_accounts_ok_imp_extract_premise >> strip_tac >>
  fs[] >>
  drule_all extract_call_result_accounts_well_typed >> simp[]
QED

Theorem run_raw_call_accounts_well_typed:
  accounts_well_typed accounts /\
  run_raw_call cx flags target_addr calldata amount accounts tStorage =
    SOME (success,retData,accounts',tStorage',emitted_logs) ==>
  accounts_well_typed accounts'
Proof
  rw[run_raw_call_def] >>
  FIRST [drule_all run_delegate_call_accounts_well_typed,
         drule_all run_ext_call_accounts_well_typed] >> simp[]
QED

(* ===== Creation adapter well-typedness =====

   Mirrors the ext-call chain above, but for run_create_evm.  The creation
   boundary reaches Verifereum through two stages: the Vyper-side account
   prelude create_prelude_accounts, and then the adapter's own result
   extraction. *)

Theorem create_accounts_runtime_well_typed_imp_extract_premise:
  !outcome.
    create_accounts_runtime_well_typed_aux
      (FST outcome) (SND outcome).rollback.accounts ==>
    (case FST outcome of
     | INR NONE => accounts_well_typed (SND outcome).rollback.accounts
     | _ => T)
Proof
  Cases >> rename1 `(result, final_state)` >>
  Cases_on `result` >>
  simp[create_accounts_runtime_well_typed_aux_def,
       accounts_runtime_well_typed_accounts_well_typed] >>
  Cases_on `y` >> simp[]
QED

Theorem extract_create_result_accounts_well_typed:
  !orig_accounts orig_tStorage pending result final_state
   code_opt accounts' tStorage' logs' revertData pending'.
    accounts_well_typed orig_accounts /\
    (case result of
     | INR NONE => accounts_well_typed final_state.rollback.accounts
     | _ => T) /\
    extract_create_result orig_accounts orig_tStorage pending
      (result, final_state) =
      SOME (code_opt, accounts', tStorage', logs', revertData, pending') ==>
    accounts_well_typed accounts'
Proof
  rw[extract_create_result_def] >>
  gvs[AllCaseEqs()]
QED


Theorem vfm_transfer_value_accounts_well_typed:
  !from to amount accounts.
    accounts_well_typed accounts /\
    amount <= (lookup_account from accounts).balance /\
    (lookup_account to accounts).balance + amount < 2 ** 256 ==>
    accounts_well_typed (vfmExecution$transfer_value from to amount accounts)
Proof
  rw[vfmExecutionTheory.transfer_value_def] >>
  gvs[accounts_well_typed_def, account_well_typed_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  first_x_assum (qspec_then `addr` mp_tac) >> decide_tac
QED


Theorem guarded_make_ext_call_state_accounts_well_typed:
  !caller callee code calldata value_opt gas accounts tStorage txParams.
    accounts_well_typed accounts /\
    ext_call_value_transfer_ok caller callee value_opt accounts ==>
    accounts_well_typed
      (make_ext_call_state caller callee code calldata value_opt gas
         accounts tStorage txParams).rollback.accounts
Proof
  rw[make_ext_call_state_def, ext_call_value_transfer_ok_def] >>
  Cases_on `value_opt` >> gvs[]
  >- simp[vfmExecutionTheory.transfer_value_def] >>
  irule vfm_transfer_value_accounts_well_typed >>
  simp[] >>
  decide_tac
QED

Theorem transfer_value_no_type_error:
  !from to amount st s.
    FST (transfer_value from to amount st) <> INR (Error (TypeError s))
Proof
  (* Original implementation proof:
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
  *)
  rpt gen_tac >> Cases_on `transfer_value from to amount st` >>
  rename1 `transfer_value from to amount st = (res,st')` >>
  Cases_on `res` >> simp[] >>
  drule concrete_send_error >> rw[]
QED

Theorem transfer_value_accounts_well_typed:
  !from to amount st.
    accounts_well_typed st.accounts ==>
    accounts_well_typed (SND (transfer_value from to amount st)).accounts
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  gvs[accounts_well_typed_def, account_well_typed_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  first_x_assum (qspec_then `addr` mp_tac) >>
  simp[vfmStateTheory.update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >> decide_tac
QED

Theorem transfer_value_runtime_consistent:
  !env cx fromAddr toAddr amount st.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (SND (transfer_value fromAddr toAddr amount st))
Proof
  rpt strip_tac >>
  Cases_on `transfer_value fromAddr toAddr amount st` >>
  rename1 `transfer_value fromAddr toAddr amount st = (res,st')` >>
  gvs[runtime_consistent_def] >>
  `st'.scopes = st.scopes` by metis_tac[transfer_value_scopes] >>
  `st'.immutables = st.immutables` by metis_tac[transfer_value_immutables] >>
  gvs[env_consistent_def, env_scopes_consistent_def,
      env_immutables_consistent_def, state_well_typed_def] >>
  rpt conj_tac >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  qspecl_then [`fromAddr`, `toAddr`, `amount`, `st`] mp_tac
    transfer_value_accounts_well_typed >>
  simp[]
QED

Theorem evaluate_abi_decode_return_well_typed:
  !tenv ret_type bs v tv.
    evaluate_abi_decode_return tenv ret_type bs = INL v /\
    evaluate_type tenv ret_type = SOME tv ==>
    value_has_type tv v
Proof
  ACCEPT_TAC vyperTypeExtCallCoreTheory.evaluate_abi_decode_return_well_typed
QED

Theorem update_accounts_transient_runtime_consistent:
  runtime_consistent env cx st /\ accounts_well_typed accounts' ==>
  runtime_consistent env cx (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  rw[runtime_consistent_def, state_well_typed_def, env_consistent_def] >>
  gvs[env_scopes_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED


(* Decoder-only boundary shared by concrete and oracle tails. Invalid bytes
   are RuntimeError, never source TypeError or control transfer. *)
Theorem extcall_decode_return_sound:
  runtime_consistent env cx st /\
  evaluate_type env.type_defs ret_type = SOME ret_tv /\
  (do
    v <- lift_sum_runtime (evaluate_abi_decode_return env.type_defs ret_type bs);
    return (Value v)
  od) st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env (Call ret_type (ExtCall stat skc fsig opts) es drv) tv
  | INR _ => T
Proof
  ACCEPT_TAC vyperTypeExtCallCoreTheory.extcall_decode_return_sound
QED

Theorem runtime_consistent_logs_append:
  !env cx st ls.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (st with logs := st.logs ++ ls)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED

Theorem append_logs_runtime_consistent:
  !env cx logs st res st'.
    runtime_consistent env cx st /\
    append_logs logs st = (res,st') ==>
    runtime_consistent env cx st'
Proof
  rw[append_logs_def, return_def] >>
  metis_tac[runtime_consistent_logs_append]
QED

Theorem env_consistent_get_tenv:
  env_consistent env cx st ==> get_tenv cx = env.type_defs
Proof
  rw[env_consistent_def, env_context_consistent_def]
QED

Theorem runtime_consistent_get_tenv:
  runtime_consistent env cx st ==> get_tenv cx = env.type_defs
Proof
  ACCEPT_TAC vyperTypeExtCallCoreTheory.runtime_consistent_get_tenv
QED

Theorem extcall_static_args_runtime_typed_dest:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: arg_tys ==>
  ?target_addr. dest_AddressV (HD vs) = SOME target_addr
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def]
QED

Theorem values_have_types_LIST_REL_extcall[local]:
  !tvs vs. values_have_types tvs vs <=> LIST_REL value_has_type tvs vs
Proof
  Induct >> Cases_on `vs` >> simp[Once value_has_type_def]
QED

Theorem LIST_REL_evaluate_expr_types[local]:
  !es tvs.
    LIST_REL (\e tv. evaluate_type tenv (expr_type e) = SOME tv) es tvs ==>
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP expr_type es) tvs
Proof
  Induct >> Cases_on `tvs` >> simp[]
QED

Theorem extcall_static_args_runtime_typed_tail:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: arg_tys ==>
  ?tvs.
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv) arg_tys tvs /\
    values_have_types tvs (TL vs)
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> Cases_on `vs` >>
  gvs[values_have_types_LIST_REL_extcall] >>
  metis_tac[LIST_REL_evaluate_expr_types]
QED

Theorem extcall_static_args_runtime_typed_nonempty:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: arg_tys ==>
  vs <> []
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `vs` >> gvs[listTheory.LIST_REL_EL_EQN]
QED

Theorem extcall_nonstatic_args_runtime_typed_dest:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  ?target_addr amount. dest_AddressV (HD vs) = SOME target_addr /\
                       dest_NumV (HD (TL vs)) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> gvs[] >>
  Cases_on `t` >> gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED


Theorem extcall_nonstatic_args_runtime_typed_tail:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  ?tvs.
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv) arg_tys tvs /\
    values_have_types tvs (TL (TL vs))
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> Cases_on `vs` >>
  gvs[values_have_types_LIST_REL_extcall] >>
  Cases_on `t` >> Cases_on `t'` >>
  gvs[values_have_types_LIST_REL_extcall] >>
  metis_tac[LIST_REL_evaluate_expr_types]
QED

Theorem extcall_nonstatic_args_runtime_typed_nonempty:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  vs <> [] /\ TL vs <> []
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `vs` >> gvs[listTheory.LIST_REL_EL_EQN] >>
  Cases_on `t` >> gvs[listTheory.LIST_REL_EL_EQN]
QED


(* Actual dispatch boundary: the prefix has already evaluated its arguments.
   The oracle default IH is applied only at the guarded adopted state. *)
Theorem well_typed_opt_THE:
  !env drv. well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)
Proof
  rpt strip_tac >>
  Cases_on `drv` >- gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `SOME drv_expr` >>
  qpat_x_assum `well_typed_opt env (SOME drv_expr)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >>
  simp[]
QED

Theorem send_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 2 /\
  HD (MAP expr_type es) = BaseT AddressT /\
  EL 1 (MAP expr_type es) = BaseT (UintT 256) ==>
  ?toAddr amount. dest_AddressV (HD vs) = SOME toAddr /\
                  dest_NumV (EL 1 vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem selfdestruct_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 1 /\
  HD (MAP expr_type es) = BaseT AddressT ==>
  ?target_addr. LENGTH vs = 1 /\
                dest_AddressV (HD vs) = SOME target_addr
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def]
QED

Theorem create_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es >= 2 /\
  HD (MAP expr_type es) = BaseT AddressT /\
  LAST (MAP expr_type es) = BaseT (UintT 256) ==>
  ?target_addr amount. vs <> [] /\
                       dest_AddressV (HD vs) = SOME target_addr /\
                       dest_NumV (LAST vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  `LENGTH vs = LENGTH es` by metis_tac[LIST_REL_LENGTH] >>
  `es <> [] /\ vs <> [] /\ tvs <> []` by (Cases_on `es` >> gvs[] >> metis_tac[LIST_REL_LENGTH]) >>
  gvs[LIST_REL_EL_EQN] >>
  `HD tvs = BaseTV AddressT` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> evaluate_type _ _ = SOME _`
      (qspec_then `0` mp_tac) >>
    Cases_on `es` >> Cases_on `tvs` >> gvs[evaluate_type_def]) >>
  `value_has_type (HD tvs) (HD vs)` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> value_has_type _ _`
      (qspec_then `0` mp_tac) >>
    Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
  `LAST tvs = BaseTV (UintT 256)` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> evaluate_type _ _ = SOME _`
      (qspec_then `PRE (LENGTH tvs)` mp_tac) >>
    Cases_on `es` >> Cases_on `tvs` >> gvs[LAST_MAP, LAST_EL, evaluate_type_def]) >>
  `value_has_type (LAST tvs) (LAST vs)` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> value_has_type _ _`
      (qspec_then `PRE (LENGTH tvs)` mp_tac) >>
    Cases_on `tvs` >> Cases_on `vs` >> gvs[LAST_EL]) >>
  Cases_on `HD vs` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `LAST vs` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem raw_call_bytes_slot_size_bound:
  n < dimword(:256) ==>
   type_slot_size (BaseTV (BytesT (Dynamic n))) <= dimword(:256) /\
   type_slot_size_list [BaseTV BoolT; BaseTV (BytesT (Dynamic n))] <= dimword(:256) /\
   type_slot_size (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))]) <= dimword(:256)
Proof
  strip_tac >>
  `type_slot_size (BaseTV (BytesT (Dynamic n))) + 2 <= dimword(:256)` by (
    `type_slot_size (BaseTV (BytesT (Dynamic n))) = 1 + (n + 31) DIV 32`
      by EVAL_TAC >>
    `(n + 31) DIV 32 <= (dimword(:256) - 1 + 31) DIV 32` by
      (irule DIV_LE_MONOTONE >> DECIDE_TAC) >>
    `(dimword(:256) - 1 + 31) DIV 32 + 3 <= dimword(:256)` by EVAL_TAC >>
    DECIDE_TAC) >>
  `type_slot_size_list [BaseTV BoolT; BaseTV (BytesT (Dynamic n))] =
   1 + type_slot_size (BaseTV (BytesT (Dynamic n)))` by EVAL_TAC >>
  `type_slot_size (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))]) =
   1 + type_slot_size (BaseTV (BytesT (Dynamic n)))` by
     simp[type_slot_size_def] >>
  DECIDE_TAC
QED

Theorem raw_call_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 3 /\
  EL 0 (MAP expr_type es) = BaseT AddressT /\
  EL 1 (MAP expr_type es) = BaseT (BytesT bd) /\
  EL 2 (MAP expr_type es) = BaseT (UintT 256) ==>
  ?target_addr data amount. dest_AddressV (HD vs) = SOME target_addr /\
                            dest_BytesV (EL 1 vs) = SOME data /\
                            dest_NumV (EL 2 vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  gvs[evaluate_type_def] >>
  Cases_on `bd` >> gvs[] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (BytesT bd_data)) v_data` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_data` >> gvs[value_has_type_def, dest_BytesV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem raw_call_calldata_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  MAP expr_type es = [BaseT AddressT; BaseT (UintT 256)] ==>
  ?target_addr amount. LENGTH vs = 2 /\
    dest_AddressV (HD vs) = SOME target_addr /\
    dest_NumV (EL 1 vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >> qexists_tac `Num i` >> simp[]
QED

(* Literal operands have their stated value even when earlier operands change
   the state. This discharges the zero-value restriction on delegate/static calls. *)
Theorem eval_exprs_EL_literal:
  !es st vs st' n ty l.
    eval_exprs cx es st = (INL vs,st') /\
    n < LENGTH es /\ EL n es = Literal ty l ==>
    EL n vs = evaluate_literal l
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  Cases_on `n` >> simp[] >> rpt strip_tac >>
  gvs[evaluate_def, return_def, materialise_def] >>
  first_x_assum drule_all >> simp[]
QED

(* Shared execution is independent of how the input bytes were obtained. *)
Theorem eval_raw_call_result_sound:
  runtime_consistent env cx st /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0) /\
  flags.rcf_max_outsize < dimword(:256) /\
  eval_raw_call cx flags target_addr calldata amount st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res /\
  (!tv e. res = INL tv /\ expr_type e = raw_call_return_type flags ==>
    expr_result_typed env e tv)
Proof
  strip_tac >> qpat_x_assum `eval_raw_call _ _ _ _ _ _ = _` mp_tac >>
  fs[eval_raw_call_def, type_check_def, assert_def, bind_def, ignore_bind_def,
       return_def, get_accounts_def, get_transient_storage_def] >>
  Cases_on `run_raw_call cx flags target_addr calldata amount
    st.accounts st.tStorage` >>
  simp[lift_option_def, bind_def, return_def, raise_def] >>
  TRY (strip_tac >> gvs[no_type_error_result_def] >> NO_TAC) >>
  PairCases_on `x` >> simp[] >>
  `accounts_well_typed x2` by (
    fs[runtime_consistent_def] >> drule_all run_raw_call_accounts_well_typed >> simp[]) >>
  `runtime_consistent env cx (st with <|accounts := x2; tStorage := x3|>)` by
    (drule_all update_accounts_transient_runtime_consistent >> simp[]) >>
  `runtime_consistent env cx
    ((st with <|accounts := x2; tStorage := x3|>) with logs := st.logs ++ x4)` by (
    qspecl_then [`env`, `cx`, `st with <|accounts := x2; tStorage := x3|>`, `x4`]
      mp_tac runtime_consistent_logs_append >> simp[]) >>
  Cases_on `x0` >> Cases_on `flags.rcf_revert_on_failure` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[update_accounts_def, update_transient_def, append_logs_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[no_type_error_result_def, expr_result_typed_def,
    expr_runtime_typed_def, toplevel_value_typed_def, value_has_type_def,
    raw_call_return_type_def, evaluate_type_def, is_HashMapRef_def] >>
  mp_tac (Q.SPEC `flags.rcf_max_outsize` (GEN_ALL raw_call_bytes_slot_size_bound)) >>
  impl_tac >- simp[] >> TRY strip_tac >>
  gvs[listTheory.LENGTH_TAKE_EQ, value_has_type_def, evaluate_type_def,
      raw_call_return_type_def] >> decide_tac
QED

Theorem raw_log_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 2 /\
  EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
  EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
  bound_at_most bd 4 ==>
  ?topics data. LENGTH vs = 2 /\
                dest_ArrayV (EL 0 vs) = SOME topics /\
                dest_BytesV (EL 1 vs) = SOME data /\
                LENGTH (case topics of
                  TupleV vs => vs | DynArrayV vs => vs | _ => []) <= 4
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[evaluate_type_def] >>
  Cases_on `bd'` >> gvs[] >>
  rename1 `value_has_type (ArrayTV (BaseTV (BytesT (Fixed 32))) bd) v_topics` >>
  rename1 `value_has_type (BaseTV (BytesT bd_data)) v_data` >>
  Cases_on `v_topics` >>
  gvs[value_has_type_def, dest_ArrayV_def] >>
  Cases_on `a` >> Cases_on `bd` >>
  gvs[value_has_type_def, bound_at_most_def, compatible_bound_def] >>
  Cases_on `v_data` >> gvs[value_has_type_def, dest_BytesV_def]
QED

Theorem accounts_well_typed_increment_nonce:
  !addr accounts.
    accounts_well_typed accounts ==>
    accounts_well_typed (vfmExecution$increment_nonce addr accounts)
Proof
  rw[accounts_well_typed_def, account_well_typed_def,
     vfmExecutionTheory.increment_nonce_def,
     vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
     combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> gvs[]
QED



Theorem runtime_consistent_increment_nonce:
  !env cx st addr.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (SND (update_accounts (vfmExecution$increment_nonce addr) st))
Proof
  rw[update_accounts_def, return_def, runtime_consistent_def,
     env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[accounts_well_typed_increment_nonce]
QED

Theorem runtime_consistent_logs_updated_by:
  !env cx st f.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (st with logs updated_by f)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED

Theorem runtime_consistent_logs_cons:
  !env cx st l.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (st with logs updated_by CONS l)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED
Theorem state_well_typed_logs_append:
  !st ls. state_well_typed st ==>
          state_well_typed (st with logs := st.logs ++ ls)
Proof
  simp[state_well_typed_def]
QED

Theorem env_consistent_logs_append:
  !env cx st ls. env_consistent env cx st ==>
                 env_consistent env cx (st with logs := st.logs ++ ls)
Proof
  rw[env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def] >>
  metis_tac[]
QED


Theorem push_log_runtime_consistent:
  !env cx l st.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (SND (push_log l st))
Proof
  rw[push_log_def, return_def] >>
  metis_tac[runtime_consistent_logs_updated_by]
QED

Theorem selfdestruct_tail_sound:
  !env cx es vs st.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 1 /\
    HD (MAP expr_type es) = BaseT AddressT ==>
    runtime_consistent env cx
      (SND ((do
               type_check (LENGTH vs = 1) "selfdestruct args";
               target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
               accounts <- get_accounts;
               self_acct <<- lookup_account cx.txn.target accounts;
               balance <<- self_acct.balance;
               transfer_value cx.txn.target target_addr balance;
               return (Value NoneV)
             od) st)) /\
    (!s. FST ((do
                 type_check (LENGTH vs = 1) "selfdestruct args";
                 target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
                 accounts <- get_accounts;
                 self_acct <<- lookup_account cx.txn.target accounts;
                 balance <<- self_acct.balance;
                 transfer_value cx.txn.target target_addr balance;
                 return (Value NoneV)
               od) st) <> INR (Error (TypeError s)))
Proof
  rpt strip_tac >>
  drule_all selfdestruct_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, get_accounts_def]
  >- (Cases_on `transfer_value cx.txn.target target_addr
          (lookup_account cx.txn.target st.accounts).balance st` >>
      gvs[return_def] >> Cases_on `q` >> gvs[] >>
      qspecl_then [`env`, `cx`, `cx.txn.target`, `target_addr`,
                   `(lookup_account cx.txn.target st.accounts).balance`, `st`]
        mp_tac transfer_value_runtime_consistent >> simp[])
  >- (qpat_x_assum `FST _ = INR (Error (TypeError s))` mp_tac >>
      rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
         raise_def, return_def, lift_option_type_def, get_accounts_def] >>
      Cases_on `transfer_value cx.txn.target target_addr
          (lookup_account cx.txn.target st.accounts).balance st` >> gvs[return_def] >>
      Cases_on `q` >> gvs[] >>
      qspecl_then [`cx.txn.target`, `target_addr`,
                   `(lookup_account cx.txn.target st.accounts).balance`, `st`, `s`]
        mp_tac transfer_value_no_type_error >> simp[])
QED

Theorem selfdestruct_tail_result_sound_simp:
  !env cx es vs st res st'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 1 /\
    HD (MAP expr_type es) = BaseT AddressT /\
    ((case type_check (LENGTH vs = 1) "selfdestruct args" st of
        (INL x,s'') =>
          (case
             (case dest_AddressV (HD vs) of
                NONE => raise (Error (TypeError "selfdestruct target"))
              | SOME v => return v) s''
           of
             (INL target_addr,s'') =>
               do
                 x <-
                   transfer_value cx.txn.target target_addr
                     (lookup_account cx.txn.target s''.accounts).balance;
                 return (Value NoneV)
               od s''
           | (INR e,s'') => (INR e,s''))
      | (INR e,s'') => (INR e,s'')) = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env (Call NoneT SelfDestructTarget es NONE) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `cx`, `es`, `vs`, `st`]
    mp_tac selfdestruct_tail_sound >>
  impl_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum `(case type_check _ _ _ of _ => _) = _` mp_tac >>
  drule_all selfdestruct_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, get_accounts_def,
     no_type_error_result_def,
     expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def, value_has_type_def,
     evaluate_type_def, is_HashMapRef_def] >>
  qpat_x_assum `(case transfer_value _ _ _ _ of _ => _) = _` mp_tac >>
  Cases_on `transfer_value cx.txn.target target_addr
      (lookup_account cx.txn.target st.accounts).balance st` >>
  Cases_on `q` >>
  rw[return_def] >>
  gvs[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
      raise_def, return_def, lift_option_type_def, get_accounts_def,
      runtime_consistent_def,
      toplevel_value_typed_def, value_has_type_def]
QED

(* ===== Shared creation helper soundness ===== *)

Theorem LIST_REL_source_value_compose[local]:
  !tys tvs.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    !vs. LIST_REL value_has_type tvs vs ==>
      LIST_REL
        (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
        tys vs
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt strip_tac >>
  Cases_on `vs` >> gvs[] >> metis_tac[]
QED

Theorem LIST_REL_APPEND_SINGLETON[local]:
  LIST_REL R (xs ++ [x]) ys ==>
  ?y ys'. ys = ys' ++ [y] /\ LIST_REL R xs ys' /\ R x y
Proof
  simp[GSYM SNOC_APPEND, LIST_REL_SNOC]
QED

Theorem exprs_runtime_typed_LIST_REL_source_value[local]:
  exprs_runtime_typed env es vs ==>
  LIST_REL
    (\ty v. ?tv. evaluate_type env.type_defs ty = SOME tv /\
                   value_has_type tv v)
    (MAP expr_type es) vs
Proof
  rw[exprs_runtime_typed_def, values_have_types_LIST_REL_extcall] >>
  drule LIST_REL_evaluate_expr_types >> strip_tac >>
  drule_all LIST_REL_source_value_compose >> simp[]
QED

Theorem source_value_LIST_REL_runtime_types[local]:
  !tys vs.
    LIST_REL
      (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
      tys vs ==>
    ?tvs.
      LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
      values_have_types tvs vs
Proof
  Induct_on `tys` >> Cases_on `vs` >>
  simp[values_have_types_LIST_REL_extcall, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `tvs` >> gvs[values_have_types_LIST_REL_extcall]
QED

Theorem value_has_type_Address_dest[local]:
  value_has_type (BaseTV AddressT) v ==>
  ?a. dest_AddressV v = SOME a
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_AddressV_def]
QED

Theorem value_has_type_Uint256_dest[local]:
  value_has_type (BaseTV (UintT 256)) v ==>
  ?n. dest_NumV v = SOME n
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem value_has_type_Bytes_dest[local]:
  value_has_type (BaseTV (BytesT bd)) v ==>
  ?bs. dest_BytesV v = SOME bs
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_BytesV_def]
QED

Theorem value_has_type_Bytes32_dest[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  ?bs. dest_BytesV v = SOME bs /\ LENGTH bs = 32
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_BytesV_def]
QED

Theorem create_args_runtime_typed_decode:
  create_arg_types_ok kind has_salt tys /\
  LIST_REL
    (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    tys vs ==>
  ?ops ctor_tys.
    dest_create_args kind has_salt vs = SOME ops /\
    create_arg_ctor_types kind has_salt tys = SOME ctor_tys /\
    LIST_REL
      (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
      ctor_tys ops.co_ctor_args
Proof
  rpt strip_tac >>
  Cases_on `kind` >> Cases_on `has_salt` >>
  gvs[create_arg_types_ok_def, dest_create_args_def,
      create_arg_ctor_types_def, make_create_operands_def,
      dest_optional_num_def, dest_optional_salt_def, dest_create_salt_def,
      evaluate_type_def, value_has_type_def, AllCaseEqs()] >>
  TRY (imp_res_tac value_has_type_Address_dest) >>
  TRY (imp_res_tac value_has_type_Uint256_dest) >>
  TRY (imp_res_tac value_has_type_Bytes32_dest) >>
  TRY (imp_res_tac value_has_type_Bytes_dest) >>
  gvs[dest_create_args_def, create_arg_ctor_types_def,
      make_create_operands_def, dest_optional_num_def,
      dest_optional_salt_def, dest_create_salt_def, AllCaseEqs()] >>
  imp_res_tac LIST_REL_APPEND_SINGLETON >>
  gvs[evaluate_type_def] >>
  qpat_x_assum `value_has_type (BaseTV (BytesT (Fixed 32))) y`
    (strip_assume_tac o MATCH_MP value_has_type_Bytes32_dest) >>
  TRY (imp_res_tac value_has_type_Bytes_dest) >>
  gvs[dest_create_args_def, create_arg_ctor_types_def,
      make_create_operands_def, dest_optional_num_def,
      dest_optional_salt_def, dest_create_salt_def,
      evaluate_type_def, value_has_type_def, GSYM SNOC_APPEND,
      AllCaseEqs()]
QED

Theorem encode_create_ctor_args_total:
  LIST_REL
    (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    tys vs ==>
  ?bytes. encode_create_ctor_args tenv tys vs = SOME bytes
Proof
  strip_tac >> drule source_value_LIST_REL_runtime_types >> strip_tac >>
  drule_all (cj 2 vyper_to_abi_total) >> strip_tac >>
  simp[encode_create_ctor_args_def]
QED

Theorem build_create_code_total:
  create_arg_types_ok kind has_salt tys /\
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt tys = SOME ctor_tys /\
  LIST_REL
    (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    ctor_tys ops.co_ctor_args ==>
  ?code_info. build_create_code tenv kind ops accounts ctor_tys blueprint_size = SOME code_info
Proof
  rpt strip_tac >>
  drule encode_create_ctor_args_total >> strip_tac >>
  Cases_on `kind` >> Cases_on `has_salt` >>
  gvs[create_arg_types_ok_def, dest_create_args_def,
      create_arg_ctor_types_def, make_create_operands_def,
      dest_optional_num_def, dest_optional_salt_def, dest_create_salt_def,
      build_create_code_def, encode_create_ctor_args_def,
      evaluate_type_def, value_has_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `b` >>
  gvs[build_create_code_def, encode_create_ctor_args_def,
      evaluate_type_def, value_has_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem lookup_account_increment_nonce_balance[simp]:
  (lookup_account a (vfmExecution$increment_nonce b accounts)).balance =
  (lookup_account a accounts).balance
Proof
  simp[vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `a = b` >> simp[]
QED


(* every account of a well-typed account map has a bounded balance; stated
   over both the lookup_account form and the raw map application so it can be
   used directly on simplified update goals *)
Theorem accounts_well_typed_balance_bound[simp]:
  !acc a. accounts_well_typed acc ==> (lookup_account a acc).balance < 2 ** 256
Proof
  rw[accounts_well_typed_def] >>
  qpat_x_assum `!addr. account_well_typed (lookup_account addr acc)`
    (qspecl_then [`a`] mp_tac) >>
  strip_tac >>
  gvs[account_well_typed_def]
QED

(* overwriting one account with a well-typed state preserves well-typedness of
   the whole map *)
Theorem accounts_well_typed_update_account:
  !address new_acct accounts.
    accounts_well_typed accounts /\ account_well_typed new_acct ==>
    accounts_well_typed (update_account address new_acct accounts)
Proof
  rw[accounts_well_typed_def, vfmStateTheory.lookup_account_def,
     vfmStateTheory.update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `address = addr` >>
  gvs[] >>
  first_assum (qspec_then `addr` strip_assume_tac) >>
  gvs[account_well_typed_def]
QED

(* the empty account is well typed *)
Theorem account_well_typed_empty_account_state:
  account_well_typed empty_account_state
Proof
  simp[account_well_typed_def, vfmStateTheory.empty_account_state_def]
QED

(* The target account is not reset: its existing balance plus the endowment
   must fit in a 256-bit word before the prelude can preserve typedness. *)
Theorem create_prelude_accounts_well_typed:
  !sender address value accounts.
    accounts_well_typed accounts /\
    value <= (lookup_account sender accounts).balance /\
    (lookup_account address accounts).balance + value < 2 ** 256 ==>
    accounts_well_typed
      (create_prelude_accounts sender address value accounts)
Proof
  rpt strip_tac >>
  simp[create_prelude_accounts_def, combinTheory.o_THM] >>
  irule vfm_transfer_value_accounts_well_typed >>
  simp[lookup_account_increment_nonce_balance,
       accounts_well_typed_increment_nonce] >>
  CONV_TAC (LAND_CONV (REWR_CONV arithmeticTheory.ADD_COMM)) >>
  qpat_x_assum `_ + value < _` mp_tac >> simp[]
QED
Theorem run_create_evm_accounts_well_typed:
  !sender address initcode value accounts tStorage pending txParams
   code_opt accounts' tStorage' logs' revertData pending'.
    accounts_well_typed accounts /\
    run_create_evm sender address initcode value accounts tStorage pending
      txParams =
      SOME (code_opt, accounts', tStorage', logs', revertData, pending') ==>
    accounts_well_typed accounts'
Proof
  rw[run_create_evm_def] >>
  gvs[AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `extract_create_result _ _ _ outcome = SOME _` >>
  PairCases_on `outcome` >>
  drule create_accounts_runtime_well_typed_imp_extract_premise >>
  strip_tac >>
  qspecl_then [`create_rollback_accounts sender accounts`, `tStorage`,
               `pending`, `outcome0`, `outcome1`, `code_opt`, `accounts'`,
               `tStorage'`, `logs'`, `revertData`, `pending'`]
    mp_tac extract_create_result_accounts_well_typed >>
  simp[create_rollback_accounts_def, accounts_well_typed_increment_nonce] >>
  gvs[]
QED

Theorem create_oracle_result_accounts_well_typed:
  accounts_well_typed st.accounts /\
  create_oracle_result salt value code rof st = (res,st') ==>
  accounts_well_typed st'.accounts
Proof
  Cases_on `salt` >> Cases_on `st.outcomes` >>
  gvs[create_oracle_result_def, vyperCallOutcomeTheory.take_create_outcome_def] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >>
  rw[vyperCallOutcomeTheory.adopt_call_outcome_equation,
     vyperCallOutcomeTheory.create_outcome_request_def] >>
  gvs[AllCaseEqs(), evaluation_state_accfupds,
      accounts_runtime_well_typed_accounts_well_typed] >>
  gvs[vyperCallOutcomeTheory.adopt_call_outcome_equation,
      vyperCallOutcomeTheory.create_outcome_request_def]
QED

Theorem eval_create_accounts_well_typed:
  accounts_well_typed st.accounts /\
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  accounts_well_typed st'.accounts
Proof
  strip_tac >>
  Cases_on `st.outcomes` >- (
  Cases_on `dest_create_args kind has_salt vs` >-
    gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys` >-
    gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, check_def, return_def,
      raise_def, AllCaseEqs()] >>
  rename1 `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size =
            SOME code_info` >>
  (* An oversized initcode failure is a RuntimeError with unchanged state. *)
  Cases_on `code_info.cc_size_ok` >>
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, update_accounts_def, get_transient_storage_def,
      get_pending_deletions_def, update_transient_def,
      update_pending_deletions_def, check_def, assert_def, return_def,
      raise_def, AllCaseEqs(), COND_RATOR,
      evaluation_state_accounts_tStorage_acc] >|
  [(* insufficient balance or nonce limit: state untouched *)
   (Cases_on `rof` >>
    gvs[create_soft_failure_def, return_def, raise_def,
        evaluation_state_accfupds]),
   (Cases_on `rof` >>
    gvs[create_soft_failure_def, return_def, raise_def,
        evaluation_state_accfupds]),
   (* address collision: only the sender nonce is bumped *)
   (Cases_on `rof` >>
    gvs[create_soft_failure_def, return_def, raise_def,
        evaluation_state_accfupds] >>
    irule accounts_well_typed_increment_nonce >> simp[]),
   (* EVM-backed creation: prelude then adapter preserve well-typedness *)
   (gvs[bind_apply, ignore_bind_apply, get_transient_storage_def,
        get_pending_deletions_def, update_accounts_def, get_accounts_def,
        return_def, AllCaseEqs(), create_soft_failure_def] >>
    qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ _ of _ => _) _`
      (fn tm => mp_tac tm) >>
    (* Both balance guards succeeded, so the prelude state is well typed. *)
    `accounts_well_typed
       (create_prelude_accounts cx.txn.target
          (create_address cx.txn.target
             (lookup_account cx.txn.target s''.accounts).nonce ops.co_salt
             code_info.cc_initcode) ops.co_value s''.accounts)` by
      (irule create_prelude_accounts_well_typed >> simp[] >> decide_tac) >>
    Cases_on `run_create_evm cx.txn.target
                (create_address cx.txn.target
                   (lookup_account cx.txn.target s''.accounts).nonce
                   ops.co_salt code_info.cc_initcode)
                code_info.cc_initcode ops.co_value s''.accounts
                s''.tStorage s''.pending_deletions
                (vyper_to_tx_params cx.txn)`
     >| [(* adapter NONE: restore the sender-only nonce increment *)
         (Cases_on `rof` >>
          gvs[create_rollback_accounts_def, create_soft_failure_def,
              bind_apply, ignore_bind_apply, update_accounts_def,
              return_def, raise_def, AllCaseEqs(),
              evaluation_state_accfupds] >>
          strip_tac >>
          irule accounts_well_typed_increment_nonce >> simp[]),
         (* adapter SOME: install adapter results; success may append logs *)
         (PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
          gvs[bind_apply, ignore_bind_apply, update_accounts_def,
              update_transient_def, update_pending_deletions_def,
              append_logs_def, return_def, raise_def, AllCaseEqs(),
              evaluation_state_accfupds] >>
          strip_tac >>
          pop_assum (fn th => REWRITE_TAC[GSYM th]) >>
          `accounts_well_typed x1` by
            (drule_all run_create_evm_accounts_well_typed >> simp[]) >>
          simp[evaluation_state_accounts_tStorage_acc,
               evaluation_state_accfupds])])]) >>
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, check_def, assert_def, return_def, raise_def,
      AllCaseEqs()] >>
  gvs[option_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  drule_all create_oracle_result_accounts_well_typed >> simp[]
QED

Theorem create_tail_result_sound_simp:
  !env cx es vs st res st' kind has_salt rof blueprint_size.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    create_arg_types_ok kind has_salt (MAP expr_type es) /\
    eval_create cx kind has_salt rof (MAP expr_type es) vs blueprint_size st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env
         (Call (BaseT AddressT) (CreateTarget kind has_salt rof kw_order) es NONE) tv
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `get_tenv cx = env.type_defs` by metis_tac[runtime_consistent_get_tenv] >>
  drule exprs_runtime_typed_LIST_REL_source_value >> strip_tac >>
  drule_all create_args_runtime_typed_decode >> strip_tac >>
  `?code_info.
      build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size =
        SOME code_info` by (
    qpat_x_assum `get_tenv cx = env.type_defs` (fn th => rewrite_tac[th]) >>
    irule build_create_code_total >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  (* No TypeError: remaining failures are runtime errors or constructor
     revert data. *)
  `!msg. res <> INR (Error (TypeError msg))` by (
    irule eval_create_no_type_error >> metis_tac[]) >>
  `accounts_well_typed st'.accounts` by (
    irule eval_create_accounts_well_typed >>
    metis_tac[runtime_consistent_def]) >>
  drule eval_create_preserves_scopes_immutables >> strip_tac >>
  `runtime_consistent env cx st'` by (
    gvs[runtime_consistent_def, state_well_typed_def, env_consistent_def,
        env_scopes_consistent_def, env_immutables_consistent_def] >>
    rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  (* the returned value is either the created address or a zero address *)
  `case res of
     | INL tv => expr_result_typed env
         (Call (BaseT AddressT) (CreateTarget kind has_salt rof kw_order) es NONE) tv
     | INR _ => T` by (
    gvs[runtime_consistent_def] >>
    qpat_x_assum `eval_create _ _ _ _ _ _ _ _ = _` mp_tac >>
    simp[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
         get_accounts_def, update_accounts_def, get_pending_deletions_def,
         check_def, assert_def, create_soft_failure_def, return_def, raise_def] >>
    rpt (IF_CASES_TAC >>
         gvs[bind_def, ignore_bind_def, update_accounts_def,
             check_def, assert_def, create_soft_failure_def,
             return_def, raise_def, expr_result_typed_def,
             expr_runtime_typed_def, expr_type_def, evaluate_type_def,
             toplevel_value_typed_def, value_has_type_def,
             is_HashMapRef_def]) >>
    rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    TRY (qpat_x_assum `create_oracle_result _ _ _ _ _ = _` mp_tac >>
         Cases_on `res` >> simp[] >> strip_tac >>
         drule create_oracle_result_address >> strip_tac >>
         gvs[toplevel_value_typed_def, value_has_type_def, is_HashMapRef_def] >> NO_TAC) >>
    first_x_assum mp_tac >>
    strip_tac >>
    gvs[get_transient_storage_def, get_pending_deletions_def,
        get_accounts_def, bind_apply, ignore_bind_apply, return_def,
        raise_def, create_soft_failure_def,
        evaluation_state_accounts_tStorage_acc] >>
qpat_x_assum
      `(case run_create_evm _ _ _ _ _ _ _ _ of _ => _) _ = _` mp_tac >>
    strip_tac >>
    (* The tail case is under-applied, i.e. `(case .. of ..) s`, so it cannot
       be unified structurally.  Split on run_create_evm directly instead --
       same sequence as eval_create_accounts_well_typed above. *)
    Cases_on `run_create_evm cx.txn.target
                (create_address cx.txn.target
                   (lookup_account cx.txn.target st.accounts).nonce
                   ops.co_salt code_info.cc_initcode)
                code_info.cc_initcode ops.co_value st.accounts
                st.tStorage st.pending_deletions (vyper_to_tx_params cx.txn)`
    >- (* adapter NONE: rollback then soft failure *)
      gs[create_rollback_accounts_def, create_soft_failure_def,
         update_accounts_def, bind_apply, ignore_bind_apply,
         raise_def, return_def, AllCaseEqs()] >>
    (* adapter SOME: install results and return an address or revert *)
    gs[] >>
    rpt (try (PairCases_on `x`)) >>
    gvs[bind_apply, ignore_bind_apply, update_accounts_def,
        update_transient_def, update_pending_deletions_def,
        append_logs_def, create_soft_failure_def,
        raise_def, return_def, AllCaseEqs()] >>
    rpt (try (Cases_on `x0`)) >>
    rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    gvs[bind_apply, ignore_bind_apply, append_logs_def, return_def,
        raise_def, evaluation_state_accounts_tStorage_acc,
        evaluation_state_accfupds, toplevel_value_typed_def,
        value_has_type_def, is_HashMapRef_def]) >>
  gvs[runtime_consistent_def]
QED

Theorem raw_revert_tail_sound:
  !env cx vs st.
    runtime_consistent env cx st /\ LENGTH vs = 1 ==>
    runtime_consistent env cx
      (SND ((do
               type_check (LENGTH vs = 1) "raw_revert args";
               raise (Error (RuntimeError "raw_revert"))
             od) st)) /\
    (!s. FST ((do
                 type_check (LENGTH vs = 1) "raw_revert args";
                 raise (Error (RuntimeError "raw_revert"))
               od) st) <> INR (Error (TypeError s)))
Proof
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def] >>
  gvs[runtime_consistent_def]
QED

Theorem raw_log_tail_sound:
  !env cx es vs st bd bd'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 2 /\
    EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
    bound_at_most bd 4 ==>
    runtime_consistent env cx
      (SND ((do
               type_check (LENGTH vs = 2) "raw_log args";
               topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
               data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
               topic_vals <<- (case topics of
                  TupleV vs => vs | DynArrayV vs => vs | _ => []);
               type_check (LENGTH topic_vals <= 4) "raw_log too many topics";
               push_log (encode_raw_event_values cx.txn.target topic_vals data);
               return (Value NoneV)
             od) st)) /\
    (!s. FST ((do
                 type_check (LENGTH vs = 2) "raw_log args";
                 topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
                 data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
                 topic_vals <<- (case topics of
                    TupleV vs => vs | DynArrayV vs => vs | _ => []);
                 type_check (LENGTH topic_vals <= 4) "raw_log too many topics";
                 push_log (encode_raw_event_values cx.txn.target topic_vals data);
                 return (Value NoneV)
               od) st) <> INR (Error (TypeError s)))
Proof
  rpt strip_tac >>
  drule_all raw_log_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  Cases_on `topics` >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, push_log_def] >>
  TRY (irule runtime_consistent_logs_append >> simp[]) >>
  qpat_x_assum `FST _ = INR (Error (TypeError s))` mp_tac >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, push_log_def]
QED

Theorem raw_log_tail_result_sound:
  !env cx es vs st res st' bd bd'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 2 /\
    EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
    bound_at_most bd 4 /\
    ((do
        type_check (LENGTH vs = 2) "raw_log args";
        topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
        data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
        topic_vals <<- (case topics of
           TupleV vs => vs | DynArrayV vs => vs | _ => []);
        type_check (LENGTH topic_vals <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target topic_vals data);
        return (Value NoneV)
      od) st = (res, st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env (Call NoneT RawLog es NONE) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `cx`, `es`, `vs`, `st`, `bd`, `bd'`]
    mp_tac raw_log_tail_sound >>
  simp[] >> strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  drule_all raw_log_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  Cases_on `topics` >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, push_log_def,
     no_type_error_result_def,
     expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def, value_has_type_def,
     evaluate_type_def, is_HashMapRef_def] >>
  gvs[runtime_consistent_def]
QED

Theorem raw_log_tail_result_sound_simp:
  !env cx es vs st topics data res st' bd bd'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 2 /\
    EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
    bound_at_most bd 4 /\
    dest_ArrayV (EL 0 vs) = SOME topics /\
    dest_BytesV (EL 1 vs) = SOME data /\
    ((case type_check (LENGTH vs = 2) "raw_log args" st of
        (INL x,s'') =>
          (case return topics s'' of
             (INL topics',s'') =>
               (case return data s'' of
                  (INL data,s'') =>
                    do
                      x <- type_check
                        (LENGTH
                           (case topics' of
                            | TupleV vs => vs
                            | DynArrayV vs' => vs'
                            | _ => []) <= 4) "raw_log too many topics";
                      x <- push_log
                        (encode_raw_event_values cx.txn.target
                          (case topics' of
                           | TupleV vs => vs
                           | DynArrayV vs' => vs'
                           | _ => []) data);
                      return (Value NoneV)
                    od s''
                | (INR e,s'') => (INR e,s''))
           | (INR e,s'') => (INR e,s''))
      | (INR e,s'') => (INR e,s'')) = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env (Call NoneT RawLog es NONE) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  qpat_x_assum `(case type_check _ _ _ of _ => _) = _` mp_tac >>
  drule_all raw_log_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  Cases_on `topics` >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def,
     lift_option_type_def, push_log_def, no_type_error_result_def,
     expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def, value_has_type_def,
     evaluate_type_def, is_HashMapRef_def] >>
  fs[type_check_def, bind_def, ignore_bind_def, assert_def, return_def,
     push_log_def] >>
  TRY (irule runtime_consistent_logs_append >> simp[]) >>
  TRY (irule state_well_typed_logs_append >> simp[]) >>
  TRY (irule env_consistent_logs_append >> simp[]) >>
  gvs[runtime_consistent_def] >>
  qpat_x_assum `(case check _ _ _ of _ => _) = _` mp_tac >>
  rw[bind_def, ignore_bind_def, check_def, assert_def, raise_def, return_def,
     lift_option_type_def, push_log_def]
QED



(* ===== extcall / staticcall / send after operand evaluation ===== *)

(* Typed ExtCall operands: the target, the positional arguments, then the
   keyword arguments, laid out as the ExtCall typing rule requires. *)
Theorem ext_call_operands_typed:
  exprs_runtime_typed env es vs /\
  MAP expr_type es =
    BaseT AddressT :: arg_types ++ MAP (ext_call_kw_type ret_type) opts ==>
  ?target_v rest target_addr arg_tvs kw_tvs.
    vs = target_v :: rest /\ dest_AddressV target_v = SOME target_addr /\
    LENGTH rest = LENGTH arg_types + LENGTH opts /\
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv) arg_types arg_tvs /\
    values_have_types arg_tvs (TAKE (LENGTH arg_types) rest) /\
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv)
      (MAP (ext_call_kw_type ret_type) opts) kw_tvs /\
    LIST_REL value_has_type kw_tvs (DROP (LENGTH arg_types) rest)
Proof
  rw[exprs_runtime_typed_def] >>
  drule LIST_REL_evaluate_expr_types >> simp[] >>
  simp[listTheory.LIST_REL_CONS1, listTheory.LIST_REL_SPLIT1] >> strip_tac >>
  gvs[listTheory.LIST_REL_CONS1, listTheory.LIST_REL_SPLIT1, evaluate_type_def] >>
  drule_all value_has_type_Address_dest >> strip_tac >>
  imp_res_tac listTheory.LIST_REL_LENGTH >>
  simp[rich_listTheory.TAKE_APPEND, listTheory.DROP_APPEND,
       values_have_types_LIST_REL_extcall] >>
  fs[listTheory.LENGTH_MAP] >> metis_tac[]
QED

(* The positional arguments may be narrower than the declared types; their
   values then also have the declared types. *)
Theorem ext_call_operands_fit_typed:
  exprs_runtime_typed env es vs /\
  MAP expr_type es =
    BaseT AddressT :: call_types ++ MAP (ext_call_kw_type ret_type) opts /\
  arg_types_fit call_types arg_types /\
  EVERY (well_formed_type env.type_defs) arg_types ==>
  ?target_v rest target_addr arg_tvs kw_tvs.
    vs = target_v :: rest /\ dest_AddressV target_v = SOME target_addr /\
    LENGTH rest = LENGTH arg_types + LENGTH opts /\
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv) arg_types arg_tvs /\
    values_have_types arg_tvs (TAKE (LENGTH arg_types) rest) /\
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv)
      (MAP (ext_call_kw_type ret_type) opts) kw_tvs /\
    LIST_REL value_has_type kw_tvs (DROP (LENGTH arg_types) rest)
Proof
  strip_tac >> drule_all ext_call_operands_typed >> strip_tac >>
  imp_res_tac arg_types_fit_LENGTH >>
  drule well_formed_types_evaluate >> strip_tac >>
  gvs[] >> qexists_tac `tvs` >> simp[] >>
  metis_tac[arg_type_fits_value_has_type]
QED

(* A keyword argument has the type its kind gives it. *)
Theorem ext_call_kwarg_typed:
  !opts kvs kw_tvs k v.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
      (MAP (ext_call_kw_type ret_type) opts) kw_tvs /\
    LIST_REL value_has_type kw_tvs kvs /\
    ext_call_kwarg k opts kvs = SOME v ==>
    ?tv. evaluate_type tenv (ext_call_kw_type ret_type k) = SOME tv /\
         value_has_type tv v
Proof
  Induct >> simp[ext_call_kwarg_def] >>
  rpt gen_tac >> Cases_on `kvs` >> simp[ext_call_kwarg_def] >>
  rw[listTheory.LIST_REL_CONS1] >> gvs[] >>
  metis_tac[]
QED

Theorem extcall_value_result_typed[local]:
  evaluate_type env.type_defs ret_type = SOME ret_tv /\ value_has_type ret_tv v ==>
  !stat skc fsig opts es drv.
    expr_result_typed env (Call ret_type (ExtCall stat skc fsig opts) es drv) (Value v)
Proof
  simp[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
       toplevel_value_typed_def, is_HashMapRef_def]
QED

Theorem extcall_decode_return_INL_typed[local]:
  runtime_consistent env cx st /\
  evaluate_type env.type_defs ret_type = SOME ret_tv /\
  evaluate_abi_decode_return env.type_defs ret_type bs = INL v ==>
  !stat skc fsig opts es drv.
    expr_result_typed env (Call ret_type (ExtCall stat skc fsig opts) es drv) (Value v)
Proof
  rpt strip_tac >>
  mp_tac (extcall_decode_return_sound |> Q.INST [`res` |-> `INL (Value v)`, `st'` |-> `st`]) >>
  asm_simp_tac (srw_ss()) [bind_def, lift_sum_runtime_def, return_def]
QED

Theorem adopt_call_outcome_INR[local]:
  (adopt_call_outcome rq co s = (INR e,s')) <=> F
Proof
  rw[vyperCallOutcomeTheory.adopt_call_outcome_def] >> pairarg_tac >> gvs[return_def]
QED

Theorem run_ext_call_update_runtime_consistent[local]:
  runtime_consistent env cx s /\
  run_ext_call caller callee calldata value_opt gas s.accounts s.tStorage txp =
    SOME result ==>
  runtime_consistent env cx
    (s with <|logs := s.logs ++ SND (SND (SND (SND result)));
              accounts := FST (SND (SND result));
              tStorage := FST (SND (SND (SND result)))|>)
Proof
  PairCases_on `result` >> rw[] >>
  `accounts_well_typed result2` by
    metis_tac[run_ext_call_accounts_well_typed, runtime_consistent_def] >>
  `runtime_consistent env cx (s with <|accounts := result2; tStorage := result3|>)`
    by metis_tac[update_accounts_transient_runtime_consistent] >>
  drule runtime_consistent_logs_append >>
  disch_then (qspec_then `result4` mp_tac) >> simp[]
QED

Theorem eval_ext_call_result_sound:
  runtime_consistent env cx st /\
  exprs_runtime_typed env es vs /\
  MAP expr_type es =
    BaseT AddressT :: call_types ++ MAP (ext_call_kw_type ret_type) opts /\
  arg_types_fit call_types arg_types /\
  EVERY (well_formed_type env.type_defs) arg_types /\
  ext_call_opts_ok static opts /\
  evaluate_type env.type_defs ret_type = SOME ret_tv /\
  eval_ext_call cx static skip_check (func_name,arg_types,ret_type) opts vs st =
    (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env
      (Call ret_type (ExtCall static skip_check (func_name,arg_types,ret_type) opts)
         es drv) tv
  | INR _ => T
Proof
  strip_tac >>
  drule_all ext_call_operands_fit_typed >> strip_tac >> gvs[] >>
  `get_tenv cx = env.type_defs` by metis_tac[runtime_consistent_get_tenv] >>
  drule_all build_ext_calldata_typed >>
  disch_then (qspec_then `func_name` strip_assume_tac) >>
  `!v. ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest) = SOME v ==>
       ?n. dest_NumV v = SOME n` by (
    rpt strip_tac >> drule_all ext_call_kwarg_typed >>
    simp[ext_call_kw_type_def, evaluate_type_def] >>
    metis_tac[value_has_type_Uint256_dest]) >>
  `!v. ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest) = SOME v ==>
       value_has_type ret_tv v` by (
    rpt strip_tac >> drule_all ext_call_kwarg_typed >>
    simp[ext_call_kw_type_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `eval_ext_call _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, check_def, lift_option_type_def, lift_option_def,
       lift_sum_runtime_def, get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def, append_logs_def,
       return_def, raise_def,
       COND_RATOR, option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
  strip_tac >>
  (* Prune value/backend branches before expanding the remaining case equations. *)
  Cases_on `static` >> gvs[] >>
  Cases_on `st.outcomes` >> gvs[] >>
  Cases_on `ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest)` >>
  gvs[] >>
  Cases_on `ext_call_precheck_ok skip_check ret_type target_addr st.accounts` >>
  gvs[] >>
  TRY (qmatch_asmsub_abbrev_tac `run_ext_call _ _ _ value_opt _ _ _ _` >>
       Cases_on `run_ext_call cx.txn.target target_addr calldata value_opt
         (forwarded_gas default_evm_gas_limit
           (ext_call_kwarg EKGas opts (DROP (LENGTH arg_types) rest)))
         st.accounts st.tStorage (vyper_to_tx_params cx.txn)` >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, adopt_call_outcome_INR] >>
  TRY (qpat_x_assum `take_call_outcome _ _ _ _ = (INR _,_)` (fn th =>
         assume_tac th >> assume_tac (MATCH_MP vyperCallOutcomePropsTheory.take_call_outcome_error th))) >>
  TRY (drule_all take_adopt_call_outcome_runtime_consistent >> strip_tac) >>
  TRY (drule_all take_call_outcome_runtime_consistent >> strip_tac) >>
  TRY (drule_all run_ext_call_update_runtime_consistent >> strip_tac) >>
  imp_res_tac extcall_value_result_typed >>
  imp_res_tac extcall_decode_return_INL_typed >>
  gvs[runtime_consistent_def, no_type_error_result_def]
QED

Theorem send_gas_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  MAP expr_type es =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) ==>
  ?to_v amount_v gas_vs toAddr amount.
    vs = to_v :: amount_v :: gas_vs /\
    LENGTH gas_vs = (if has_gas then 1 else 0) /\
    dest_AddressV to_v = SOME toAddr /\ dest_NumV amount_v = SOME amount
Proof
  Cases_on `has_gas` >> rw[exprs_runtime_typed_def] >>
  gvs[listTheory.MAP_EQ_CONS, listTheory.LIST_REL_CONS1, evaluate_type_def] >>
  metis_tac[value_has_type_Uint256_dest, value_has_type_Address_dest]
QED

Theorem eval_send_result_sound:
  runtime_consistent env cx st /\
  exprs_runtime_typed env es vs /\
  MAP expr_type es =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) /\
  eval_send cx has_gas vs st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env (Call NoneT (Send has_gas) es drv) tv
  | INR _ => T
Proof
  strip_tac >>
  drule_all send_gas_args_runtime_typed_dest >> strip_tac >>
  gvs[] >>
  qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [eval_send_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, lift_option_type_def, LET_THM] >>
  Cases_on `st.outcomes` >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def] >> strip_tac
  >- (gvs[get_accounts_def, get_transient_storage_def, lift_option_def,
          check_def, assert_def, update_accounts_def, update_transient_def,
          append_logs_def, bind_def, ignore_bind_def, return_def, raise_def,
          option_CASE_rator, AllCaseEqs()] >>
      TRY (drule_all run_ext_call_update_runtime_consistent >> strip_tac) >>
      gvs[runtime_consistent_def, no_type_error_result_def, expr_result_typed_def,
           expr_runtime_typed_def, expr_type_def, toplevel_value_typed_def,
           value_has_type_def, evaluate_type_def, is_HashMapRef_def]) >>
  drule_all (Send_outcome_type_sound |>
    SRULE [bind_def, ignore_bind_def, return_def]) >> simp[]
QED
