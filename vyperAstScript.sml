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
  | AddressT
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
  | Lt
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
  | ArrayLit (bound option (* NONE for tuples *)) (expr list)
  | Subscript expr expr
  | Attribute expr identifier
  (* TODO: short-circuiting builtins *)
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
  | Assign assignment_target expr
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
  function_mutability
  = Pure
  | View
  | Nonpayable
  | Payable
End

Datatype:
  variable_visibility = Public | Private
End

Datatype:
  variable_mutability = Constant expr | Immutable | Transient | Storage
End

Type argument = “:identifier # type”;

Datatype:
  value_type = Type type | HashMapT type value_type
End

Datatype:
  toplevel
  = FunctionDef function_visibility function_mutability identifier (argument list) type (stmt list)
  | VariableDecl variable_visibility variable_mutability identifier type
  | StructDef identifier (argument list)
  | HashMapDecl identifier type value_type
End

val () = export_theory();
