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
  (* TODO: add Tuple *)
  | ArrayLit (expr list)
  | Subscript expr expr
  | Compare expr cmpop expr
  | BinOp expr operator expr
End

Datatype:
  base_assignment_target
  = NameTarget identifier
  | SubscriptTarget base_assignment_target expr
  | AttributeTarget base_assignment_target identifier
End

Datatype:
  assignment_target
  = BaseTarget base_assignment_target
  | TupleTarget (assignment_target list)
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
  | Assign assignment_target expr (* TODO: allow tuple rhs *)
  | AugAssign identifier (* TODO: or subscript or attribute? *) operator expr
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

Definition function_body_def:
  function_body (FunctionDef _ _ _ body _) = body
End

val () = export_theory();
