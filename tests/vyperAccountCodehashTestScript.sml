(* Empty-account codehash boundaries, with independent Keccak test vectors.
   EVAL and CV exercise the same account items used by account_items_program. *)
Theory vyperAccountCodehashTest
Ancestors
  vyperContext vfmState vfmExecution vyperTypeBuiltins
Libs
  cv_transLib wordsLib

Definition codehash_test_account_def:
  codehash_test_account balance nonce code = empty_account_state with
    <| balance := balance; nonce := nonce; code := code |>
End
val () = cv_auto_trans codehash_test_account_def;

(* Storage is irrelevant to EVM account emptiness. *)
Theorem codehash_empty_account_boundary:
  a.balance = 0 /\ a.nonce = 0 /\ a.code = [] ==>
  evaluate_account_op Codehash bs a = BytesV (REPLICATE 32 0w)
Proof
  simp[evaluate_account_op_def, account_empty_def]
QED

Theorem codehash_empty_code_nonempty_account_boundary:
  a.code = [] /\ (a.balance <> 0 \/ a.nonce <> 0) ==>
  evaluate_account_op Codehash bs a = BytesV (Keccak_256_w64 [])
Proof
  rw[evaluate_account_op_def, account_empty_def]
QED

Theorem codehash_nonempty_code_boundary:
  a.code <> [] ==>
  evaluate_account_op Codehash bs a = BytesV (Keccak_256_w64 a.code)
Proof
  Cases_on `a.code` >> simp[evaluate_account_op_def, account_empty_def]
QED

Theorem codehash_empty_account_eval:
  evaluate_account_op Codehash [] empty_account_state =
    BytesV (REPLICATE 32 0w)
Proof
  EVAL_TAC
QED

Theorem codehash_empty_code_balance_nonce_eval:
  evaluate_account_op Codehash [] (codehash_test_account 1 0 []) =
    BytesV (word_to_bytes_be
      (0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470w:bytes32)) /\
  evaluate_account_op Codehash [] (codehash_test_account 0 1 []) =
    BytesV (word_to_bytes_be
      (0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470w:bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem codehash_nonempty_code_eval:
  evaluate_account_op Codehash [] (codehash_test_account 0 0 [0w]) =
    BytesV (word_to_bytes_be
      (0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98aw:bytes32))
Proof
  CONV_TAC cv_eval
QED

(* The actual Acc builtin uses lookup_account, including a missing/empty
   account. Its type annotation and address width are the fixture's ones. *)
Theorem codehash_builtin_cv_boundaries:
  evaluate_builtin empty_evaluation_context (K empty_account_state)
    (BaseT (BytesT (Fixed 32))) (Acc Codehash) tys [BytesV (REPLICATE 20 0w)] =
    INL (BytesV (REPLICATE 32 0w)) /\
  evaluate_builtin empty_evaluation_context (K (codehash_test_account 1 0 []))
    (BaseT (BytesT (Fixed 32))) (Acc Codehash) tys [BytesV (REPLICATE 20 0w)] =
    INL (BytesV (word_to_bytes_be
      (0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470w:bytes32))) /\
  evaluate_builtin empty_evaluation_context (K (codehash_test_account 0 1 []))
    (BaseT (BytesT (Fixed 32))) (Acc Codehash) tys [BytesV (REPLICATE 20 0w)] =
    INL (BytesV (word_to_bytes_be
      (0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470w:bytes32))) /\
  evaluate_builtin empty_evaluation_context (K (codehash_test_account 0 0 [0w]))
    (BaseT (BytesT (Fixed 32))) (Acc Codehash) tys [BytesV (REPLICATE 20 0w)] =
    INL (BytesV (word_to_bytes_be
      (0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98aw:bytes32)))
Proof
  simp[evaluate_builtin_def, lookup_account_def] >> CONV_TAC cv_eval
QED

(* The other account operations retain their exact values. *)
Theorem account_other_items_unchanged:
  evaluate_account_op Address bs a = BytesV bs /\
  evaluate_account_op Balance bs a = IntV &a.balance /\
  evaluate_account_op Codesize bs a = IntV &LENGTH a.code /\
  evaluate_account_op IsContract bs a = BoolV (a.code <> []) /\
  evaluate_account_op Code bs a = BytesV a.code
Proof
  simp[evaluate_account_op_def]
QED
