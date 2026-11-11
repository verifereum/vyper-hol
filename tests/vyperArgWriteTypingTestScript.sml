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

(* Only the constructor may write an immutable ("Immutable value cannot be
   written to" in vyper/semantics/analysis/local.py); an internal function
   it calls may not. *)
Definition imm_env_def:
  imm_env vis =
    function_entry_env
      (add_toplevel_static_maps T NONE
         (VariableDecl Private Immutable "x" (BaseT BoolT) NONE)
         empty_contract_type_artifact) [] NONE vis []
End

Definition imm_assign_def:
  imm_assign =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"x")))
       (Literal (BaseT BoolT) (BoolL T))]
End

Theorem internal_immutable_write_rejected:
  type_stmts (imm_env Internal) NoneT imm_assign = NONE /\
  type_stmts (imm_env External) NoneT imm_assign = NONE
Proof
  EVAL_TAC
QED

Theorem deploy_immutable_write_accepted:
  IS_SOME (type_stmts (imm_env Deploy) NoneT imm_assign)
Proof
  EVAL_TAC >> simp[]
QED
