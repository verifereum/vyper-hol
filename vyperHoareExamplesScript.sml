Theory vyperHoareExamples

Ancestors
  vyperHoare

(* Valid transfer parameters: amount parameter is within uint256 bounds
   This is guaranteed by abi_to_vyper during external call setup, but we
   need it as an explicit precondition since valid_erc20_state only validates storage *)
Definition valid_transfer_params_def:
  valid_transfer_params cx (st : evaluation_state) <=>
    ?amt. eval_expr cx (Name "amount") st = (INL (Value (IntV (Unsigned 256) amt)), st) /\
          within_int_bound (Unsigned 256) amt
End

Definition erc20_transfer_def:
  erc20_transfer = [
    Assert (Builtin (Bop GtE) [Subscript (TopLevelName (NONE, "balances")) (Builtin (Env Sender) []); Name "amount"]) (Literal (StringL 5 "error"));
    AugAssign (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
                              (Builtin (Env Sender) [])) Sub (Name "amount");
    AugAssign (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
                              (Name "to")) Add (Name "amount");
    Return (SOME (Literal (BoolL T)))
  ]
End

Definition example_1_def:
  example_1 = [
    AnnAssign "x" (BaseT (IntT 128)) (Literal (IntL (Signed 128) 10));
    AnnAssign "y" (BaseT (IntT 128)) (Name "x");
  ]
End
