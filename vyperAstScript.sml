open HolKernel boolLib bossLib Parse wordsLib;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val () = new_theory "vyperAst";

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
  | BytesT
End

Datatype:
  literal
  = BoolL bool
  | StringL string
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
  | Raise string
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

val () = export_theory();
