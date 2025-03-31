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
  = UintT num (* bit size *)
  | IntT num
  | BoolT
  | DecimalT
  | StringT num
  | BytesT bound
  | AddressT
End

Datatype:
  type
  = BaseT base_type
  | TupleT (type list)
  | ArrayT type bound
  | StructT identifier
  | FlagT identifier
  | NoneT
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
  | Div
  | Mod
End

Datatype:
  message_item
  = Sender
  | SelfAddr
  | ValueSent
End

Datatype:
  account_item
  = Balance
End

Datatype:
  builtin
  = Len
  | Eq
  | Not
  | Lt
  | Bop binop
  | Msg message_item
  | Acc account_item
End

Datatype:
  call_target
  = IntCall identifier
  | ExtCall identifier (* external call passing Vyper values *)
  | Send
  (* TODO: external raw call *)
End

Datatype:
  expr
  = Name identifier
  | TopLevelName identifier
  | FlagMember identifier identifier
  | IfExp expr expr expr
  | Literal literal
  | ArrayLit bound (expr list)
  | StructLit identifier ((identifier # expr) list)
  | Subscript expr expr
  | Attribute expr identifier
  | Builtin builtin (expr list)
  (* TODO: add the `in` operator *)
  (* TODO: ensure `in` on literals short-circuits (or decide about that..) *)
  | Call call_target (expr list)
End

Datatype:
  base_assignment_target
  = NameTarget identifier
  | TopLevelNameTarget identifier
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
  | For identifier type expr (* TODO also range *) num (stmt list)
  | If expr (stmt list) (stmt list)
  (* TODO: add Log *)
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
  = FunctionDecl function_visibility function_mutability identifier (argument list) type (stmt list)
  | VariableDecl variable_visibility variable_mutability identifier type
  | StructDecl identifier (argument list)
  | HashMapDecl variable_visibility identifier type value_type
  | FlagDecl identifier (identifier list)
  (* TODO: interfaces -- would these be a no-op except for type-checking? *)
End

Overload uint256 = “BaseT (UintT 256)”
Overload address = “BaseT AddressT”
Overload bool = “BaseT BoolT”
Overload li = “λi. Literal (IntL i)”
Overload lb = “λb. Literal (BoolL b)”
Overload "==" = “λe1 e2. Builtin Eq [e1; e2]”
Overload "not" = “λe. Builtin Not [e]”
Overload "or" = “λe1 e2. IfExp e1 (lb T) e2”
Overload "and" = “λe1 e2. IfExp e1 e2 (lb F)”
(* TODO: make "or" and "and" infix *)
Overload "+" = “λe1 e2. Builtin (Bop Add) [e1; e2]”
Overload "<" = “λe1 e2. Builtin Lt [e1; e2]”
Overload len = “λe. Builtin Len [e]”
Overload def = “λid args ret body. FunctionDecl External Nonpayable id args ret body”
Overload itl_def = “λid args ret body. FunctionDecl Internal Nonpayable id args ret body”
Overload pay_def = “λid args ret body. FunctionDecl External Payable id args ret body”
Overload deploy_def = “λid args ret body. FunctionDecl Deploy Nonpayable id args ret body”
Overload pubvar = “λid typ. VariableDecl Public Storage id typ”
Overload pubmap = “λid kt vt. HashMapDecl Public id kt vt”
Overload privar = “λid typ. VariableDecl Private Storage id typ”
Overload DynArray = “λt n. ArrayT t (Dynamic n)”
Overload DynArlit = “λn ls. ArrayLit (Dynamic n) ls”
Overload msg_sender = “Builtin (Msg Sender) []”
Overload msg_value = “Builtin (Msg ValueSent) []”
Overload AssignSelf = “λid e. Assign (BaseTarget (TopLevelNameTarget id)) e”
Overload self_ = “λid. TopLevelName id”
Overload self = “Builtin (Msg SelfAddr) []”
Overload self_balance = “Builtin (Acc Balance) [self]”
Overload call = “λid args. Call (IntCall id) args”

val () = export_theory();
