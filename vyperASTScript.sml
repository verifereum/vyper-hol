Theory vyperAST
Ancestors
  string words
Libs
  cv_transLib

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
  | DecimalL int
End

Datatype:
  binop
  = Add
  | Sub
  | Mul
  | Div
  | UAdd
  | USub
  | UMul
  | UDiv
  | ExpMod
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
  | LtE
  | Gt
  | GtE
  | Min
  | Max
End

Datatype:
  env_item
  = Sender
  | SelfAddr
  | ValueSent
  | TimeStamp
  | BlockNumber
  | BlobBaseFee
  | GasPrice
  | PrevHash
End

Datatype:
  account_item
  = Address
  | Balance
  | Codehash
  | Codesize
  | IsContract
  | Code
End

Datatype:
  denomination
  = Wei
  | Kwei
  | Mwei
  | Gwei
  | Szabo
  | Finney
  | Ether
  | KEther
  | MEther
  | GEther
  | TEther
End

Datatype:
  builtin
  = Len
  | Not
  | Neg
  | Keccak256
  | AsWeiValue denomination
  | Concat num (* dynamic bound for return type *)
  | Slice num (* ditto *)
  | Uint2Str num (* ditto *)
  | MakeArray (type option (* NONE for tuples *)) bound
  | Ceil
  | Floor
  | AddMod
  | MulMod
  | Bop binop
  | BlockHash
  | BlobHash
  | Env env_item
  | Acc account_item
  | Isqrt
  (* Elliptic curve cryptography - precompile builtins *)
  | ECRecover    (* ecrecover(hash, v, r, s) -> address *)
  | ECAdd        (* ecadd((x1,y1), (x2,y2)) -> (x3,y3) on BN254 *)
  | ECMul        (* ecmul((x,y), scalar) -> (x',y') on BN254 *)
End

Datatype:
  call_target
  = IntCall (num option) identifier (* source_id (NONE=self), func_name *)
  | ExtCall identifier (* external call passing Vyper values *)
  | Send
  (* TODO: external raw call *)
End

Datatype:
  type_builtin = Empty | MaxValue | MinValue | Epsilon | Convert | Extract32
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
  (* interfaces not included, since this AST is for typechecked code *)
End

(* some helper functions over the AST datatypes *)

Definition is_Constant_def[simp]:
  is_Constant (Constant _) = T ∧
  is_Constant _ = F
End

val () = cv_auto_trans is_Constant_def;

Definition is_Unsigned_def[simp]:
  (is_Unsigned (Unsigned _ ) = T) ∧
  (is_Unsigned _ = F)
End

val () = cv_auto_trans is_Unsigned_def;

Definition int_bound_bits_def[simp]:
  int_bound_bits (Unsigned b) = b ∧
  int_bound_bits (Signed b) = b
End

val () = cv_trans int_bound_bits_def;

Definition is_TupleT_def[simp]:
  is_TupleT (TupleT _) = T ∧
  is_TupleT _ = F
End

val () = cv_auto_trans is_TupleT_def;

Definition is_ArrayT_def[simp]:
  is_ArrayT (ArrayT _ _) = T ∧
  is_ArrayT _ = F
End

val () = cv_auto_trans is_ArrayT_def;

Definition ArrayT_type_def[simp]:
  ArrayT_type (ArrayT t _) = t ∧
  ArrayT_type _ = NoneT
End

val () = cv_auto_trans ArrayT_type_def;
