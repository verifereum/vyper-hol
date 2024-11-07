open HolKernel boolLib bossLib Parse wordsLib;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val _ = new_theory "vyperAst";

Type identifier = “:string”;

Datatype:
  type
  = Uint word5 (* the bit size divided by 8 *)
  | Int word5
  | Tuple (type list)
  | DynArray type num
  | Void
  | Bool
End

Datatype:
  literal
  = Str string
  | Hex string
  | Bytes (word8 list)
  | Int int
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
    AnnAssign "a" (Uint (n2w (256 DIV 8))) (Literal (Int 1));
    If (Compare (Name "a") Eq (Literal (Int 1)))
    [
      Assign "a" (Literal (Int 2))
    ]
    [
      Assign "a" (Literal (Int 3))
    ];
    Return (SOME (BinOp (Name "a") Add (Literal (Int 42))))
  ] (Uint (n2w (256 DIV 8)))
End

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast =
  FunctionDef "foo" [External] []
  [
     AnnAssign "a" (DynArray (Uint (n2w (256 DIV 8))) 10)
       (ArrayLit [Literal (Int 1); Literal (Int 2); Literal (Int 3)]);
     AnnAssign "counter" (Uint (n2w (256 DIV 8))) (Literal (Int 0));
     For "i" (Uint (n2w (256 DIV 8))) (Name "a")
     [ OpAssign "counter" Add (Name "i") ]
  ]
End

val _ = export_theory();
