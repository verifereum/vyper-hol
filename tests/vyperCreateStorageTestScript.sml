Theory vyperCreateStorageTest
Ancestors
  vyperCreateSelfdestruct vyperCreate vyperInterpreter
  vyperSmallStep[ignore_grammar] vfmExecution vfmState
Libs
  cv_transLib wordsLib

Definition storage_create_expr_def:
  storage_create_expr salted rof initcode =
    Call (BaseT AddressT) (CreateTarget RawCreate salted rof)
      ([blueprint_test_raw_arg initcode;
        Literal (BaseT (UintT 256)) (IntL 5)] ++
       (if salted then
         [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w))]
       else [])) NONE
End
val () = cv_auto_trans storage_create_expr_def;

Definition storage_create_address_def:
  storage_create_address salted initcode =
    create_address 41w 2 (if salted then SOME 0w else NONE) initcode
End
val () = cv_auto_trans storage_create_address_def;

Definition storage_create_state_def:
  storage_create_state salted oracle initcode nonce code =
    let st = blueprint_test_state [] in
    st with
      <|accounts := update_account (storage_create_address salted initcode)
          (empty_account_state with
            <|balance := 7; nonce := nonce; code := code;
              storage := update_storage 0w 17w
                (update_storage 9w 23w empty_storage)|>) st.accounts;
        outcomes := if oracle then SOME [] else NONE|>
End
val () = cv_auto_trans storage_create_state_def;

(* Check the recursive and CPS evaluators on real EVM initcode in both outcome
   modes. Creation does not consume an external-call oracle entry. *)
Definition storage_create_observation_def:
  storage_create_observation salted oracle rof initcode nonce code =
    let st = storage_create_state salted oracle initcode nonce code in
    let e = storage_create_expr salted rof initcode in
    let r = blueprint_test_run e st in
    let final = SND r in
    let sender = lookup_account 41w final.accounts in
    let target = lookup_account (storage_create_address salted initcode)
          final.accounts in
    (eval_expr blueprint_test_context e st = r /\
     final.logs = st.logs /\ final.requests = st.requests /\
     final.outcomes = st.outcomes,
     FST r, sender.nonce, sender.balance, target.nonce, target.balance,
     lookup_storage 0w target.storage, lookup_storage 9w target.storage,
     target.code)
End
val () = storage_create_observation_def
  |> SRULE [vyperSmallStepTheory.eval_expr_eq_cont_cps,
            GSYM blueprint_test_run_def]
  |> cv_auto_trans;

Theorem storage_only_create_clears_storage_preserves_balance:
  EVERY (\salted. EVERY (\oracle.
    storage_create_observation salted oracle T [0w] 0 [] =
      (T, INL (Value (AddressV (storage_create_address salted [0w]))),
       3, 95, 1, 12, 0w, 0w, [])) [F;T]) [F;T]
Proof
  simp[listTheory.EVERY_DEF] >> rpt conj_tac >|
    [CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval]
QED

(* PUSH0 SLOAD PUSH0 MSTORE PUSH1 32 PUSH0 RETURN: the deposited bytes expose
   the value the constructor read, before any constructor storage writes. *)
Definition storage_reading_initcode_def:
  storage_reading_initcode : byte list =
    [0x5fw;0x54w;0x5fw;0x52w;0x60w;32w;0x5fw;0xf3w]
End
val () = cv_auto_trans storage_reading_initcode_def;

Theorem storage_only_create_initcode_reads_zero:
  EVERY (\salted. EVERY (\oracle.
    storage_create_observation salted oracle T storage_reading_initcode 0 [] =
      (T, INL (Value (AddressV
         (storage_create_address salted storage_reading_initcode))),
       3, 95, 1, 12, 0w, 0w, REPLICATE 32 0w)) [F;T]) [F;T]
Proof
  simp[listTheory.EVERY_DEF] >> rpt conj_tac >|
    [CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval]
QED

(* Write slot zero, then REVERT. Both the prelude's wipe and the constructor's
   write must roll back, together with the endowment. *)
Definition storage_reverting_initcode_def:
  storage_reverting_initcode : byte list =
    [0x60w;99w;0x5fw;0x55w;0x5fw;0x5fw;0xfdw]
End
val () = cv_auto_trans storage_reverting_initcode_def;

Theorem storage_only_create_revert_restores_storage_and_balance:
  EVERY (\salted. EVERY (\oracle. EVERY (\rof.
    storage_create_observation salted oracle rof
      storage_reverting_initcode 0 [] =
      (T, if rof then INR (Error (RevertData []))
          else INL (Value (AddressV 0w)),
       3, 100, 0, 7, 17w, 23w, [])) [F;T]) [F;T]) [F;T]
Proof
  simp[listTheory.EVERY_DEF] >> rpt conj_tac >|
    [CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval]
QED

Theorem nonce_or_code_collision_preserves_storage_and_balance:
  EVERY (\salted. EVERY (\oracle. EVERY (\rof.
    EVERY (\(nonce,code).
      storage_create_observation salted oracle rof [0w] nonce code =
        (T, if rof then INR (Error (RuntimeError "create address collision"))
            else INL (Value (AddressV 0w)),
         3, 100, nonce, 7, 17w, 23w, code))
      [(1,[]); (0,[0w])]) [F;T]) [F;T]) [F;T]
Proof
  simp[listTheory.EVERY_DEF] >> rpt conj_tac >|
    [CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval,
     CONV_TAC cv_eval]
QED
