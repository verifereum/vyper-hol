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
  int_bound
  = Signed num
  | Unsigned num
End

Datatype:
  literal
  = BoolL bool
  | StringL num string
  | BytesL bound (word8 list)
  | IntL int_bound int
End

Datatype:
  binop
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  | Exp
  | And
  | Or
  | XOr
  | ShL
  | ShR
  | In
  | NotIn
  | Eq
  | NotEq
  | Lt
  | Gt
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
  | Codehash
  | Codesize
  | IsContract
  | Code
End

Datatype:
  builtin
  = Len
  | Not
  | Neg
  | Keccak256
  | Concat num (* return type dynamic bound *)
  | Slice num (* ditto *)
  | MakeArray bound
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
  type_builtin = Empty | MaxValue | MinValue | Epsilon | Convert
End

Datatype:
  expr
  = Name identifier
  | TopLevelName identifier
  | FlagMember identifier identifier
  | IfExp expr expr expr
  | Literal literal
  | StructLit identifier ((identifier # expr) list)
  | Subscript expr expr
  | Attribute expr identifier
  | Builtin builtin (expr list)
  | TypeBuiltin type_builtin type (expr list)
  | Pop base_assignment_target
  | Call call_target (expr list)
; base_assignment_target
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
  iterator
  = Array expr
  | Range expr expr (* start end; use Literal (IntL (Unsigned 256) 0) for start when missing *)
  (* the For syntax always includes a bound *)
  (* for Array, this should be derived from the type of the expression *)
  (* for Range, if the bound is not given explicitly, use end - start (which
   * should both be literal integers) *)
End

Datatype:
  stmt
  = Pass
  | Continue
  | Break
  | Expr expr
  | For identifier type iterator num (stmt list)
  | If expr (stmt list) (stmt list)
  | Assert expr expr
  | Log identifier (expr list)
  | Raise expr
  | Return (expr option)
  | Assign assignment_target expr
  | AugAssign base_assignment_target binop expr
  | Append base_assignment_target expr
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
  | HashMapDecl variable_visibility bool (* transient? *) identifier type value_type
  | StructDecl identifier (argument list)
  | EventDecl identifier (argument list)
  | FlagDecl identifier (identifier list)
  (* TODO: interfaces -- would these be a no-op except for type-checking? *)
End

Overload uint256 = “BaseT (UintT 256)”
Overload address = “BaseT AddressT”
Overload bool = “BaseT BoolT”
Overload li = “λb i. Literal (IntL b i)”
Overload lb = “λb. Literal (BoolL b)”
Overload "==" = “λe1 e2. Builtin (Bop Eq) [e1; e2]”
Overload "not" = “λe. Builtin Not [e]”
Overload "or" = “λe1 e2. IfExp e1 (lb T) e2”
Overload "and" = “λe1 e2. IfExp e1 e2 (lb F)”
(* TODO: make "or" and "and" infix *)
Overload "+" = “λe1 e2. Builtin (Bop Add) [e1; e2]”
Overload "<" = “λe1 e2. Builtin (Bop Lt) [e1; e2]”
Overload ">" = “λe1 e2. Builtin (Bop Gt) [e1; e2]”
Overload len = “λe. Builtin Len [e]”
Overload def = “λid args ret body. FunctionDecl External Nonpayable id args ret body”
Overload itl_def = “λid args ret body. FunctionDecl Internal Nonpayable id args ret body”
Overload pay_def = “λid args ret body. FunctionDecl External Payable id args ret body”
Overload deploy_def = “λid args ret body. FunctionDecl Deploy Nonpayable id args ret body”
Overload pubvar = “λid typ. VariableDecl Public Storage id typ”
Overload pubmap = “λid kt vt. HashMapDecl Public id kt vt”
Overload privar = “λid typ. VariableDecl Private Storage id typ”
Overload DynArray = “λt n. ArrayT t (Dynamic n)”
Overload DynArlit = “λn ls. Builtin (MakeArray (Dynamic n)) ls”
Overload msg_sender = “Builtin (Msg Sender) []”
Overload msg_value = “Builtin (Msg ValueSent) []”
Overload AssignSelf = “λid e. Assign (BaseTarget (TopLevelNameTarget id)) e”
Overload assign = “λt e. Assign (BaseTarget t) e”
Overload return = “λe. Return $ SOME e”
Overload sub = “λt e. SubscriptTarget t e”
Overload self_ = “λid. TopLevelName id”
Overload self = “Builtin (Msg SelfAddr) []”
Overload self_balance = “Builtin (Acc Balance) [self]”
Overload call = “λid args. Call (IntCall id) args”

val () = export_theory();
