(* Concrete source executions for the strict synthetic call bound. *)
Theory sourceCallCountWitnessTest
Ancestors
  sourceCallCount vyperInterpreter vyperSmallStep vyperCreate vyperCallOutcome
  vyperRuntimeAccounts vyperState vyperContext vyperValue extCallOracle
  vfmState vfmContext list words combin option
Libs cv_transLib wordsLib

val () = fn_entry_run_def
  |> SRULE [eval_external_defaults_run, eval_exprs_eq_cont_cps,
            eval_stmts_eq_cont_cps, set_scopes_def,
            vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
            vyperStateTheory.return_def, vyperStateTheory.raise_def,
            LET_THM, COND_RATOR, vyperMiscTheory.option_CASE_rator,
            get_transient_storage_def, update_transient_def]
  |> cv_auto_trans;

val () = cv_auto_trans call_entry_run_def;

Definition source_count_copy_expr_def:
  source_count_copy_expr =
    Call (BaseT AddressT) (CreateTarget CreateCopyOf F F [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [42w]));
       Literal (BaseT (UintT 256)) (IntL 0)] NONE
End
val () = cv_auto_trans source_count_copy_expr_def;

Definition source_count_copy_program_def:
  source_count_copy_program =
    [FunctionDecl External Nonpayable F F "f" [] [] NoneT
       [Expr source_count_copy_expr; Expr source_count_copy_expr]]
End
val () = cv_auto_trans source_count_copy_program_def;

Definition source_count_copy_machine_def:
  source_count_copy_machine = initial_machine_state with
    <|sources := [(1w, [(NONE, source_count_copy_program)])];
      accounts := update_account 42w
        (empty_account_state with code := [0w]) empty_accounts|>
End
val () = cv_auto_trans source_count_copy_machine_def;

Definition source_count_copy_tx_def:
  source_count_copy_tx = empty_call_txn with
    <|target := 1w; function_name := "f"|>
End
val () = cv_auto_trans source_count_copy_tx_def;

Theorem nonce_probe_passes_create_account_guard:
  accounts_runtime_well_typed
    (K (empty_account_state with nonce := 2 ** 64))
Proof
  simp[probe_failed_outcome_def, empty_failed_outcome_def,
       accounts_runtime_well_typed_def, account_runtime_well_typed_def,
       lookup_account_def, empty_account_state_def]
QED

Theorem balance_probe_fails_create_account_guard:
  ~accounts_runtime_well_typed probe_failed_outcome.co_accounts
Proof
  simp[probe_failed_outcome_def, empty_failed_outcome_def,
       accounts_runtime_well_typed_def, account_runtime_well_typed_def,
       lookup_account_def, empty_account_state_def]
QED

Definition source_count_copy_actual_observe_def:
  source_count_copy_actual_observe =
  ((case call_entry_run [] [] source_count_copy_machine source_count_copy_tx of
     NONE => F
   | SOME (res, st) =>
       res = INL () /\
       MAP (\rq. rq.cr_kind) st.requests = [CreateCall; CreateCall] /\
       st.outcomes = SOME []) /\
  (case call_external (SOME []) [] source_count_copy_machine source_count_copy_tx of
     (res, am, rqs) =>
       res = INL NoneV /\
       MAP (\rq. rq.cr_kind) rqs = [CreateCall; CreateCall]))
End
val () = cv_auto_trans source_count_copy_actual_observe_def;

Theorem exhausted_actual_entry_runs_two_creates:
  (case call_entry_run [] [] source_count_copy_machine source_count_copy_tx of
     NONE => F
   | SOME (res, st) =>
       res = INL () /\
       MAP (\rq. rq.cr_kind) st.requests = [CreateCall; CreateCall] /\
       st.outcomes = SOME []) /\
  (case call_external (SOME []) [] source_count_copy_machine source_count_copy_tx of
     (res, am, rqs) =>
       res = INL NoneV /\
       MAP (\rq. rq.cr_kind) rqs = [CreateCall; CreateCall])
Proof
  REWRITE_TAC [GSYM source_count_copy_actual_observe_def] >> CONV_TAC cv_eval
QED


Theorem nonce_accounts_ok[local]:
  accounts_runtime_well_typed
    (K <|nonce := n; balance := 0; storage := K 0w; code := []|>)
Proof
  simp[accounts_runtime_well_typed_def, account_runtime_well_typed_def,
       lookup_account_def]
QED

Theorem copy_accounts_ok[local]:
  accounts_runtime_well_typed
    ((42w =+ <|nonce := 0; balance := 0; storage := K 0w; code := [0w]|>)
      empty_accounts)
Proof
  simp[accounts_runtime_well_typed_def, account_runtime_well_typed_def,
       lookup_account_def, empty_accounts_def, APPLY_UPDATE_THM] >>
  gen_tac >> Cases_on `42w = addr` >>
  simp[empty_accounts_def, empty_account_state_def]
QED

Theorem probe_accounts_bad[local]:
  ~accounts_runtime_well_typed
    (K <|nonce := 0; balance := 2 ** 256; storage := K 0w; code := []|>)
Proof
  simp[accounts_runtime_well_typed_def, account_runtime_well_typed_def,
       lookup_account_def]
QED

val probe_accounts_bad_eval =
  CONV_RULE
    (computeLib.RESTR_EVAL_CONV [``accounts_runtime_well_typed``])
    probe_accounts_bad;

Theorem copy_oracle_only[local]:
  IS_SOME st.outcomes /\ ~cx.txn.is_static ==>
  eval_create cx CreateCopyOf F F [BaseT AddressT; BaseT (UintT 256)]
    [BytesV bs; IntV 0] NONE st =
  (case dest_AddressV (BytesV bs) of
     NONE => (INR (Error (TypeError "create operand shape")), st)
   | SOME target =>
       if (lookup_account target st.accounts).code = []
       then (INR (Error (RuntimeError "create source has no deployable code")), st)
       else create_oracle_result NONE 0
         (create_copy_initcode (lookup_account target st.accounts).code) F st)
Proof
  strip_tac >>
  Cases_on `dest_AddressV (BytesV bs)` >>
  simp[eval_create_def, dest_create_args_def, make_create_operands_def,
       create_arg_ctor_types_def, dest_optional_num_def, dest_optional_salt_def,
       dest_NumV_def, lift_option_type_def, lift_option_def,
       bind_def, ignore_bind_def, return_def, raise_def, get_accounts_def,
       build_create_code_def, check_def, assert_def, check_not_static_def] >>
  rw[] >> gvs[]
QED

fun copy_oracle_conv facts tm =
  let val (head,args) = strip_comb tm in
    if is_const head andalso same_const head ``eval_create`` andalso
       length args = 8 then
      let val matched = PART_MATCH (lhs o snd o dest_imp) copy_oracle_only tm
          val premise = fst (dest_imp (concl matched))
          val rewritten = MP matched
            (EQT_ELIM (SIMP_CONV (srw_ss()) facts premise))
      in CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) facts)) rewritten end
    else NO_CONV tm
  end;

fun COPY_ORACLE_TAC (g as (asl,_)) =
  CONV_TAC (ONCE_DEPTH_CONV (copy_oracle_conv (map ASSUME asl))) g;

Theorem balance_probe_rejects_two_create_boundary:
  ~source_calls_within 2 source_count_copy_machine source_count_copy_tx [] []
Proof
  `dest_AddressV (BytesV
    [0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;42w]) =
     SOME (42w:address)` by CONV_TAC cv_eval >>
  computeLib.RESTR_EVAL_TAC [``call_entry_run``] >>
  computeLib.RESTR_EVAL_TAC [``eval_stmts``] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  COPY_ORACLE_TAC >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
  computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
  EVAL_TAC
QED

val zero_entry_machine =
  ``source_count_copy_machine with sources :=
      [(1w,[(NONE,[FunctionDecl External Nonpayable F F "f" [] [] NoneT []])])]``;

val precompile_entry_machine =
  ``source_count_copy_machine with sources :=
      [(1w,[(NONE,[FunctionDecl External Nonpayable F F "f" [] [] NoneT
        [Expr (Builtin (BaseT AddressT) ECRecover
          [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w));
           Literal (BaseT (UintT 256)) (IntL 0);
           Literal (BaseT (UintT 256)) (IntL 0);
           Literal (BaseT (UintT 256)) (IntL 0)])]])])]``;

Theorem entered_zero_call_boundary:
  ~source_calls_within 0 ^zero_entry_machine source_count_copy_tx [] [] /\
  source_calls_within 1 ^zero_entry_machine source_count_copy_tx [] []
Proof
  EVAL_TAC
QED

Theorem exhausted_precompile_entry_has_no_request:
  (case call_entry_run [] [] ^precompile_entry_machine source_count_copy_tx of
     SOME (res,st) =>
       res = INR (Error (RuntimeError "precompile failed")) /\
       st.requests = [] /\ st.outcomes = SOME []
   | NONE => F) /\
  (case call_external (SOME []) [] ^precompile_entry_machine source_count_copy_tx of
     (res,am,rqs) =>
       res = INR (Error (RuntimeError "precompile failed")) /\ rqs = [])
Proof
  EVAL_TAC
QED

Theorem exhausted_precompile_call_boundary:
  ~source_calls_within 1 ^precompile_entry_machine source_count_copy_tx [] [] /\
  source_calls_within 2 ^precompile_entry_machine source_count_copy_tx [] []
Proof
  EVAL_TAC
QED

(* Share the request-specific replay outcome rather than expanding nested runs. *)
val copy_request =
  ``<| cr_kind := CreateCall; cr_gas := NONE; cr_data_len := 12;
       cr_target := 0w; cr_value := 0;
       cr_data := [98w;0w;0w;1w;61w;129w;96w;11w;61w;57w;243w;0w];
       cr_static := F; cr_accounts := source_count_copy_machine.accounts;
       cr_tStorage := empty_transient_storage |>``;
val copy_failure = ``failed_outcome ^copy_request``;

fun COPY_OBSERVE_TAC g =
  ( `dest_AddressV (BytesV
      [0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;42w]) =
       SOME (42w:address)` by CONV_TAC cv_eval >>
    computeLib.RESTR_EVAL_TAC [``eval_stmts``] >>
    computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
    COPY_ORACLE_TAC >>
    computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
    PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
    computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
    COPY_ORACLE_TAC >>
    computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``] >>
    PURE_REWRITE_TAC [nonce_accounts_ok, copy_accounts_ok, probe_accounts_bad_eval] >>
    computeLib.RESTR_EVAL_TAC [``eval_create``, ``accounts_runtime_well_typed``]) g;

Theorem copy_first_marker[local]:
  case call_entry_run [probe_failed_outcome] []
         source_count_copy_machine source_count_copy_tx of
    NONE => F
  | SOME (res,st) =>
      res = INR (Error (RuntimeError "create outcome accounts")) /\
      st.outcomes = SOME [] /\ ~NULL st.requests /\
      LAST st.requests = ^copy_request
Proof
  COPY_OBSERVE_TAC
QED

Theorem copy_first_empty[local]:
  case call_entry_run [empty_failed_outcome] []
         source_count_copy_machine source_count_copy_tx of
    NONE => F
  | SOME (res,st) =>
      res <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  COPY_OBSERVE_TAC
QED

Theorem copy_second_marker[local]:
  case call_entry_run [^copy_failure; probe_failed_outcome] []
         source_count_copy_machine source_count_copy_tx of
    NONE => F
  | SOME (res,st) =>
      res = INR (Error (RuntimeError "create outcome accounts")) /\
      st.outcomes = SOME [] /\ ~NULL st.requests /\
      LAST st.requests = ^copy_request
Proof
  COPY_OBSERVE_TAC
QED

Theorem copy_second_empty[local]:
  case call_entry_run [^copy_failure; empty_failed_outcome] []
         source_count_copy_machine source_count_copy_tx of
    NONE => F
  | SOME (res,st) =>
      res <> INR (Error (RuntimeError "create outcome accounts"))
Proof
  COPY_OBSERVE_TAC
QED

Theorem copy_third_marker_unused[local]:
  case call_entry_run [^copy_failure; ^copy_failure; probe_failed_outcome] []
         source_count_copy_machine source_count_copy_tx of
    NONE => F
  | SOME (res,st) => st.outcomes <> SOME []
Proof
  COPY_OBSERVE_TAC
QED

Theorem balance_probe_accepts_two_creates_with_room:
  source_calls_within 3 source_count_copy_machine source_count_copy_tx [] []
Proof
  mp_tac copy_first_marker >> mp_tac copy_first_empty >>
  mp_tac copy_second_marker >> mp_tac copy_second_empty >>
  mp_tac copy_third_marker_unused >>
  rpt strip_tac >>
  Cases_on `call_entry_run [probe_failed_outcome] []
    source_count_copy_machine source_count_copy_tx` >> gvs[] >>
  rename1 `SOME result = call_entry_run _ _ _ _` >>
  PairCases_on `result` >> gvs[] >>
  Cases_on `call_entry_run [empty_failed_outcome] []
    source_count_copy_machine source_count_copy_tx` >> gvs[] >>
  rename1 `SOME result = call_entry_run _ _ _ _` >>
  PairCases_on `result` >> gvs[] >>
  Cases_on `call_entry_run [^copy_failure; probe_failed_outcome] []
    source_count_copy_machine source_count_copy_tx` >> gvs[] >>
  rename1 `SOME result = call_entry_run _ _ _ _` >>
  PairCases_on `result` >> gvs[] >>
  Cases_on `call_entry_run [^copy_failure; empty_failed_outcome] []
    source_count_copy_machine source_count_copy_tx` >> gvs[] >>
  rename1 `SOME result = call_entry_run _ _ _ _` >>
  PairCases_on `result` >> gvs[] >>
  Cases_on `call_entry_run [^copy_failure; ^copy_failure; probe_failed_outcome] []
    source_count_copy_machine source_count_copy_tx` >> gvs[] >>
  rename1 `SOME result = call_entry_run _ _ _ _` >>
  PairCases_on `result` >> gvs[] >>
  simp[source_calls_within_def, entry_calls_within_def] >>
  rewrite_tac[numLib.num_CONV ``3``, numLib.num_CONV ``2``,
              numLib.num_CONV ``1``] >>
  rpt (qpat_x_assum `SOME _ = call_entry_run _ _ _ _`
          (assume_tac o SYM)) >>
  simp[entry_calls_within_from_def]
QED
