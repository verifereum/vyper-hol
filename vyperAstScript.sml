open HolKernel boolLib bossLib Parse wordsLib;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val _ = new_theory "vyperAst";

Type identifier = “:string”;

Datatype:
  type
  = UintT word5 (* the bit size divided by 8 *)
  | IntT word5
  | TupleT (type list)
  | DynArrayT type num
  | VoidT
  | BoolT
  | StringT
  | HexT
  | BytesT
End

Datatype:
  literal
  = StrL string
  | HexL string
  | BytesL (word8 list)
  | IntL int
End

Datatype:
  cmpop
  = Eq
  | NotEq
End

Datatype:
  operator
  = Add
  | Sub
End

Datatype:
  expr
  = NamedExpr expr expr
  | Name identifier
  | IfExp expr expr expr
  | Literal literal
  | ArrayLit (expr list)
  | Compare expr cmpop expr
  | BinOp expr operator expr
End

Datatype:
  stmt
  = Pass
  | Continue
  | Break
  | For identifier type expr (stmt list)
  | If expr (stmt list) (stmt list)
  | Assert expr string
  | Raise (string option)
  | Return (expr option)
  | Assign identifier (* TODO: could be a tuple *) expr
  | OpAssign identifier operator expr
  | AnnAssign identifier type expr
End

Datatype:
  decorator
  = External
  | Internal
End

Type argument = “:string # type”;

Datatype:
  toplevel
  = FunctionDef string (decorator list) (argument list) (stmt list) type
End

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

val _ = export_theory();
