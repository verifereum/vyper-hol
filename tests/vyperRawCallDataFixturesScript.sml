(* Shared fixed ASTs, not a second implementation of the checker. *)
Theory vyperRawCallDataFixtures
Ancestors
  vyperTypeContract

Definition raw_data_flags_def:
  raw_data_flags =
    <|rcf_max_outsize := 0; rcf_is_delegate := F; rcf_is_static := F;
      rcf_revert_on_failure := T; rcf_kws := []|>
End

Definition raw_data_modules_def:
  (raw_data_modules payload_ty : (num option # toplevel list) list) =
    [(NONE, [FunctionDecl External Nonpayable F F "f"
       [("target", BaseT AddressT); ("payload", payload_ty)] [] NoneT
       [Expr (Call NoneT (RawCallTarget raw_data_flags)
         [Name (BaseT AddressT) "target"; Name payload_ty "payload"] NONE)]])]
End

Definition raw_empty_modules_def:
  (raw_empty_modules : (num option # toplevel list) list) =
    [(NONE, [FunctionDecl External Nonpayable F F "f"
       [("target", BaseT AddressT)] [] NoneT
       [Expr (Call NoneT (RawCallTarget raw_data_flags)
         [Name (BaseT AddressT) "target";
          Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])] NONE)]])]
End
