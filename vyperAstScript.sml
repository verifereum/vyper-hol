open HolKernel boolLib bossLib Parse wordsLib;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val () = new_theory "vyperAst";

Type identifier = “:string”;

Datatype:
  bound
  = Fixed num
  | Dynamic num
End

Datatype:
  base_type
  = UintT word5 (* the bit size divided by 8 *)
  | IntT word5
  | BoolT
  (* TODO: decimals? *)
  | StringT num
  (* TODO: flags *)
  | BytesT bound
  (* TODO: address *)
End

Datatype:
  type
  = BaseT base_type
  | TupleT (type list)
  | ArrayT type bound
  | StructT identifier
  | VoidT (* for functions with no return type *)
End

Datatype:
  literal
  = BoolL bool
  | StringL num string
  | BytesL bound (word8 list)
  | IntL int
End

Datatype:
  binop
  = Add
  | Sub
  | Mul
End

Datatype:
  builtin
  = Len
  | Eq
  | Not
  | Bop binop
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
  | ArrayLit bound (expr list)
  | Subscript expr expr
  | Attribute expr identifier
  | Builtin builtin (expr list)
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
  | Expr expr
  | For identifier type expr num (stmt list)
  | If expr (stmt list) (stmt list)
  | Assert expr string
  | Raise string
  | Return (expr option)
  | Assign assignment_target expr (* TODO: allow tuple rhs *)
  | AugAssign base_assignment_target binop expr
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
  | StructDef identifier (argument list)
End

Definition function_body_def:
  function_body (FunctionDef _ _ _ _ body) = body ∧
  function_body _ = []
End

val () = export_theory();
