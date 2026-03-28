Theory vyperAST
Ancestors
  string words
Libs
  cv_transLib

Type identifier = “:string”;

(* Namespaced identifier: (source_id, name) where NONE = self, SOME n = module *)
Type nsid = “:num option # identifier”;

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
  | StringL string
  | BytesL (word8 list)
  | IntL int
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
  | ChainId
  | Coinbase
  | GasLimit
  | BaseFee
  | PrevRandao
  | TxOrigin
  | MsgGas
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
  | Abs           (* abs(x): absolute value with overflow check *)
  | Keccak256
  | Sha256
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
  | MethodId (* compute 4-byte function selector from signature string *)
  (* Elliptic curve cryptography - precompile builtins *)
  | ECRecover    (* ecrecover(hash, v, r, s) -> address *)
  | ECAdd        (* ecadd((x1,y1), (x2,y2)) -> (x3,y3) on BN254 *)
  | ECMul        (* ecmul((x,y), scalar) -> (x',y') on BN254 *)
  | PowMod256   (* pow_mod256(base, exp) -> (base ** exp) % 2^256 *)
End

(* Resolved external call signature: (func_name, arg_types, return_type) *)
Type ext_call_sig = “:identifier # (type list) # type”;

Datatype:
  raw_call_flags = <|
    rcf_max_outsize: num
  ; rcf_is_delegate: bool
  ; rcf_is_static: bool
  ; rcf_revert_on_failure: bool
  |>
End

(* Which variant of CREATE to use *)
Datatype:
  create_kind
  = CreateMinimalProxy  (* create_minimal_proxy_to(target) *)
  | CreateCopyOf        (* create_copy_of(target) *)
  | CreateFromBlueprint num bool (* code_offset, raw_args *)
                        (* create_from_blueprint(target, *args) *)
  | RawCreate           (* raw_create(bytecode, *args) *)
End

Datatype:
  call_target
  = IntCall nsid
  | ExtCall bool ext_call_sig (* is_static, resolved signature *)
                              (* is_static: T for staticcall (read-only), F for extcall *)
                              (* Convention for Call (ExtCall is_static sig) args:
                                 - staticcall (T): args = [target; arg1; arg2; ...]
                                 - extcall (F):    args = [target; value; arg1; arg2; ...]
                                 where target is address and value is uint256 to send *)
  | Send
  (* raw_call(to, data, max_outsize=0, gas=gas, value=0, ...)
     args = [to_addr; data_bytes; value]
     Keyword args (compile-time constants) are in raw_call_flags *)
  | RawCallTarget raw_call_flags
  (* raw_log(topics, data)
     args = [data_bytes; topic1; ...; topicN] where N ≤ 4 *)
  | RawLog
  (* raw_revert(data) — terminus
     args = [data_bytes] *)
  | RawRevert
  (* selfdestruct(to) — terminus
     args = [to_addr] *)
  | SelfDestructTarget
  (* create_*(target, *ctor_args, value=0, salt=NONE, revert_on_failure=T)
     args = [target_or_bytecode; ctor_arg1; ...; value]
     salt: NONE = CREATE, SOME s = CREATE2 with salt s *)
  | CreateTarget create_kind bool (* revert_on_failure *)
End

Datatype:
  type_builtin = Empty | MaxValue | MinValue | Epsilon | Convert | Extract32 | AbiDecode | AbiEncode
End

Datatype:
  expr
  = Name type identifier              (* local/scoped variable *)
  | BareGlobalName type identifier    (* constant or immutable, looked up by bare name *)
  | TopLevelName type nsid            (* module-qualified global: self.x, lib.x *)
  | FlagMember type nsid identifier
  | IfExp type expr expr expr
  | Literal type literal
  | StructLit type nsid ((identifier # expr) list)
  | Subscript type expr expr
  | Attribute type expr identifier
  | Builtin type builtin (expr list)
  | TypeBuiltin type type_builtin type (expr list)
      (* 1st type: result type of the expression *)
      (* 2nd type: type argument to the builtin (e.g., target type for Convert) *)
  | Pop type base_assignment_target
  | Call type call_target (expr list) (expr option)
      (* expr list: arguments -- see ExtCall above for conventions *)
      (* expr option: default return value *)
; base_assignment_target
  = NameTarget identifier              (* local/scoped variable target *)
  | BareGlobalNameTarget identifier    (* immutable target (assignment only during __init__) *)
  | TopLevelNameTarget nsid            (* module-qualified global target *)
  | SubscriptTarget base_assignment_target expr
  | AttributeTarget base_assignment_target identifier
End

Definition expr_type_def:
  (expr_type (Name ty _) = ty) /\
  (expr_type (BareGlobalName ty _) = ty) /\
  (expr_type (TopLevelName ty _) = ty) /\
  (expr_type (FlagMember ty _ _) = ty) /\
  (expr_type (IfExp ty _ _ _) = ty) /\
  (expr_type (Literal ty _) = ty) /\
  (expr_type (StructLit ty _ _) = ty) /\
  (expr_type (Subscript ty _ _) = ty) /\
  (expr_type (Attribute ty _ _) = ty) /\
  (expr_type (Builtin ty _ _) = ty) /\
  (expr_type (TypeBuiltin ty _ _ _) = ty) /\
  (expr_type (Pop ty _) = ty) /\
  (expr_type (Call ty _ _ _) = ty)
End

Datatype:
  assignment_target
  = BaseTarget base_assignment_target
  | TupleTarget (assignment_target list)
End

Datatype:
  iterator
  = Array expr
  | Range expr expr (* start end; use Literal (BaseT (UintT 256)) (IntL 0) for start when missing *)
  (* the For syntax always includes a bound *)
  (* for Array, this should be derived from the type of the expression *)
  (* for Range, if the bound is not given explicitly, use end - start (which
   * should both be literal integers) *)
End

Datatype:
  assert_reason
  = AssertBare                (* simple assert, no reason *)
  | AssertUnreachable         (* assert UNREACHABLE → INVALID opcode *)
  | AssertReason expr         (* assert with Error(string) reason *)
End

Datatype:
  raise_reason
  = RaiseBare                 (* bare raise: revert 0,0 *)
  | RaiseUnreachable          (* raise UNREACHABLE → INVALID opcode *)
  | RaiseReason expr          (* raise with Error(string) reason *)
End

Datatype:
  stmt
  = Pass
  | Continue
  | Break
  | Expr expr
  | For identifier type iterator num (stmt list)
  | If expr (stmt list) (stmt list)
  | Assert expr assert_reason
  | Log nsid (expr list)
  | Raise raise_reason
  | Return (expr option)
  | Assign assignment_target expr
  | AugAssign type base_assignment_target binop expr
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

(* Interface function signature: name, args, return type, mutability *)
Type interface_func = “:identifier # (argument list) # type # function_mutability”;

Datatype:
  value_type = Type type | HashMapT type value_type
End

Datatype:
  toplevel
  = FunctionDecl function_visibility function_mutability bool (* nonreentrant *)
      identifier (argument list) (expr list) type (stmt list)
  | VariableDecl variable_visibility variable_mutability identifier type
  | HashMapDecl variable_visibility bool (* transient? *) identifier type value_type
  | StructDecl identifier (argument list)
  | EventDecl identifier ((argument # bool) list)  (* bool = indexed *)
  | FlagDecl identifier (identifier list)
  | InterfaceDecl identifier (interface_func list)
End

(* some helper functions over the AST datatypes *)

Theorem bound_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperAST",Tyop="bound"}));

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

Definition bound_length_def[simp]:
  bound_length (Fixed n) = n ∧
  bound_length (Dynamic n) = n
End

val () = cv_trans bound_length_def;

Definition int_bound_bits_def[simp]:
  int_bound_bits (Unsigned b) = b ∧
  int_bound_bits (Signed b) = b
End

val () = cv_trans int_bound_bits_def;

Definition type_to_int_bound_def:
  type_to_int_bound (BaseT (UintT n)) = SOME (Unsigned n) ∧
  type_to_int_bound (BaseT (IntT n)) = SOME (Signed n) ∧
  type_to_int_bound _ = NONE
End

val () = cv_auto_trans type_to_int_bound_def;

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
