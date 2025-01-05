open HolKernel boolLib bossLib Parse wordsLib;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val () = new_theory "vyperAst";

Type identifier = “:string”;

Datatype:
  base_type
  = UintT word5 (* the bit size divided by 8 *)
  | IntT word5
  | BoolT
  (* TODO: decimals? *)
  | StringT (* TODO: length limit *)
  (* TODO: fixed-size bytes *)
  (* TODO: flags *)
  | BytesT (* TODO: length limit *)
  (* TODO: address *)
End

Datatype:
  type
  = BaseT base_type
  | TupleT (type list)
  | DynArrayT type num
  (* TODO: fixed-size lists *)
  | VoidT (* TODO: is this needed? *)
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
  (*
  = NamedExpr expr expr
  *)
  = Name identifier
  | GlobalName identifier
  | IfExp expr expr expr
  | Literal literal
  (* TODO: add Tuple *)
  | ArrayLit (expr list)
  | Subscript expr expr
  | Attribute expr identifier
  | Compare expr cmpop expr
  | BinOp expr operator expr
  | Call identifier (expr list)
End

Datatype:
  base_assignment_target
  = NameTarget identifier
  | GlobalNameTarget identifier
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
  function_visibility
  = External
  | Internal
  | Deploy
End

Datatype:
  variable_visibility = Public | Private
End

Datatype:
  mutability = Constant expr | Immutable | Transient | Storage
End

Type argument = “:identifier # type”;

Datatype:
  toplevel
  = FunctionDef identifier function_visibility (argument list) type (stmt list)
  | VariableDecl identifier type variable_visibility mutability
End

Definition function_body_def:
  function_body (FunctionDef _ _ _ _ body) = body ∧
  function_body _ = []
End

val () = export_theory();
