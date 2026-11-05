Theory vyperArgWriteTypingTest
Ancestors
  vyperTypeContract

(* Vyper rejects writes to the arguments of external and deploy functions
   ("Cannot write to calldata"); internal-function arguments are writable. *)

Definition arg_env_def:
  arg_env vis =
    function_entry_env empty_contract_type_artifact [] NONE vis
      [("x", BaseT (UintT 256))]
End

Definition arg_assign_def:
  arg_assign =
    [Assign (BaseTarget (NameTarget "x")) (Literal (BaseT (UintT 256)) (IntL 1))]
End

Definition arg_augassign_def:
  arg_augassign =
    [AugAssign (BaseT (UintT 256)) (NameTarget "x") Add
       (Literal (BaseT (UintT 256)) (IntL 1))]
End

Theorem external_and_deploy_arg_writes_rejected:
  type_stmts (arg_env External) NoneT arg_assign = NONE /\
  type_stmts (arg_env External) NoneT arg_augassign = NONE /\
  type_stmts (arg_env Deploy) NoneT arg_assign = NONE /\
  type_stmts (arg_env Deploy) NoneT arg_augassign = NONE
Proof
  EVAL_TAC
QED

Theorem internal_arg_writes_accepted:
  IS_SOME (type_stmts (arg_env Internal) NoneT arg_assign) /\
  IS_SOME (type_stmts (arg_env Internal) NoneT arg_augassign)
Proof
  EVAL_TAC >> simp[]
QED
