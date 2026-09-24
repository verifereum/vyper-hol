(*
 * Compiler subset fixtures for supported control-flow, deployment, and spill
 * interactions. These programs are exact copies of the audited TASK_090 HOL
 * frontend translations.
 *)
Theory evalCompilerSubsetControlDeploy
Ancestors evalCompiler

Definition function_modes_program_def:
  function_modes_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl Deploy Nonpayable F F "__init__"
       [("seed", BaseT (UintT 256))] ([] : expr list) NoneT
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Name (BaseT (UintT 256)) "seed")];
     FunctionDecl External Pure F F "pure_pick"
       [("flag", BaseT BoolT); ("a", BaseT (UintT 256));
        ("b", BaseT (UintT 256))]
       ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (IfExp (BaseT (UintT 256)) (Name (BaseT BoolT) "flag")
            (Name (BaseT (UintT 256)) "a")
            (Name (BaseT (UintT 256)) "b")))];
     FunctionDecl External View F F "read_stored"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))];
     FunctionDecl External Payable F F "paid_value"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Env ValueSent) []))];
     FunctionDecl External Nonpayable F F "write_stored"
       [("v", BaseT (UintT 256))] ([] : expr list) NoneT
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Name (BaseT (UintT 256)) "v")];
     FunctionDecl External Payable F F "__default__"
       ([] : (string # type) list) ([] : expr list) NoneT
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Builtin (BaseT (UintT 256)) (Env ValueSent) [])]]
End

Definition assert_raise_program_def:
  assert_raise_program =
    [FunctionDecl External Pure F F "assert_bare"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assert
          (Builtin (BaseT BoolT) (Bop NotEq)
            [Name (BaseT (UintT 256)) "x";
             Literal (BaseT (UintT 256)) (IntL 0)])
          AssertBare;
        Return (SOME (Name (BaseT (UintT 256)) "x"))];
     FunctionDecl External Pure F F "assert_reason"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assert
          (Builtin (BaseT BoolT) (Bop NotEq)
            [Name (BaseT (UintT 256)) "x";
             Literal (BaseT (UintT 256)) (IntL 0)])
          (AssertReason
            (Literal (BaseT (StringT 4)) (StringL "zero")));
        Return (SOME (Name (BaseT (UintT 256)) "x"))];
     FunctionDecl External Pure F F "raise_bare"
       [("flag", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [If (Name (BaseT BoolT) "flag") [Raise RaiseBare] [];
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))];
     FunctionDecl External Pure F F "raise_reason"
       [("flag", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [If (Name (BaseT BoolT) "flag")
          [Raise (RaiseReason
             (Literal (BaseT (StringT 3)) (StringL "bad")))] [];
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]
End

(* Evaluator-small exact-parity partitions of assert_raise_program. *)
Definition assert_bare_program_def:
  assert_bare_program = TAKE 1 assert_raise_program
End

Definition assert_reason_program_def:
  assert_reason_program =
    [FunctionDecl External Pure F F "assert_reason"
       ([] : (string # type) list) ([] : expr list) NoneT
       [Assert (Literal (BaseT BoolT) (BoolL F))
          (AssertReason
            (Literal (BaseT (StringT 1)) (StringL "x")))]]
End

Definition raise_bare_program_def:
  raise_bare_program = TAKE 1 (DROP 2 assert_raise_program)
End

Definition raise_reason_program_def:
  raise_reason_program =
    [FunctionDecl External Pure F F "raise_reason"
       ([] : (string # type) list) ([] : expr list) NoneT
       [Raise (RaiseReason
          (Literal (BaseT (StringT 1)) (StringL "x")))]]
End

Definition loops_program_def:
  loops_program =
    [FunctionDecl External Pure F F "sum_fixed"
       [("xs", ArrayT (BaseT (UintT 256)) (Fixed 4))]
       ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "total" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "x" (BaseT (UintT 256))
          (Array
            (Name (ArrayT (BaseT (UintT 256)) (Fixed 4)) "xs")) 4
          [AugAssign (BaseT (UintT 256)) (NameTarget "total") Add
             (Name (BaseT (UintT 256)) "x")];
        Return (SOME (Name (BaseT (UintT 256)) "total"))];
     FunctionDecl External Pure F F "sum_dynamic"
       [("n", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "total" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Name (BaseT (UintT 256)) "n")) 8
          [AugAssign (BaseT (UintT 256)) (NameTarget "total") Add
             (Name (BaseT (UintT 256)) "i")];
        Return (SOME (Name (BaseT (UintT 256)) "total"))]]
End

val _ = export_theory ();
