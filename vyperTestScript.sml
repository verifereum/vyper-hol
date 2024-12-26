open HolKernel boolLib bossLib Parse;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast =
  FunctionDef "foo" [External] []
  [
    AnnAssign "a" (UintT (n2w (256 DIV 8))) (Literal (IntL 1));
    If (Compare (Name "a") Eq (Literal (IntL 1)))
    [
      Assign "a" (Literal (IntL 2))
    ]
    [
      Assign "a" (Literal (IntL 3))
    ];
    Return (SOME (BinOp (Name "a") Add (Literal (IntL 42))))
  ] (UintT (n2w (256 DIV 8)))
End

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast =
  FunctionDef "foo" [External] []
  [
     AnnAssign "a" (DynArrayT (UintT (n2w (256 DIV 8))) 10)
       (ArrayLit [Literal (IntL 1); Literal (IntL 2); Literal (IntL 3)]);
     AnnAssign "counter" (UintT (n2w (256 DIV 8))) (Literal (IntL 0));
     For "i" (UintT (n2w (256 DIV 8))) (Name "a")
     [ OpAssign "counter" Add (Name "i") ]
  ]
End

val () = export_theory();
