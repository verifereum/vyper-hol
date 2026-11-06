(* A successful child with address zero still returns the CREATE failure word. *)
Theory createOracleResultTest
Ancestors
  vyperCreate vyperCallOutcome vyperRuntimeAccounts vyperState vyperValue
  extCallOracle

Theorem create_oracle_zero_address_uses_failure_branch:
  !st rq rof.
    accounts_runtime_well_typed rq.cr_accounts ==>
    FST (create_oracle_result NONE 0 [] rof
      (st with outcomes := SOME
        [failed_outcome rq with co_success := T])) =
    (if rof then INR (Error (RevertData []))
     else INL (Value (AddressV 0w)))
Proof
  rpt strip_tac >> Cases_on `rof` >>
  simp[create_oracle_result_def, take_create_outcome_def,
       take_outcome_def, failed_outcome_def]
QED
