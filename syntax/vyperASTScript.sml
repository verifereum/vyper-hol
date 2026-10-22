Theory vyperAST
Ancestors
  ASCIInumbers string words arithmetic sorting vyperMisc[ignore_grammar]
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
  | StructT nsid
  | FlagT nsid
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
  | UnsafeAdd
  | UnsafeSub
  | UnsafeMul
  | UnsafeDiv
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
  | CalldataLen (* len(msg.data): complete calldata, including selector *)
  | CalldataSlice num (* literal positive length; sole operand is start *)
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

(* The generated size equation is stated over the record constructor, but the
   frontend builds the flags with record-update syntax, which CBV cannot match
   against it; this accessor form computes on both. *)
Theorem raw_call_flags_size_accessors[compute]:
  !r. raw_call_flags_size r =
        1 + (r.rcf_max_outsize + (bool_size r.rcf_is_delegate +
             (bool_size r.rcf_is_static + bool_size r.rcf_revert_on_failure)))
Proof
  Cases >>
  REWRITE_TAC [DB.fetch "-" "raw_call_flags_size_def",
               DB.fetch "-" "raw_call_flags_accessors"]
QED

(* Which variant of CREATE to use *)
Datatype:
  create_kind
  = CreateMinimalProxy  (* create_minimal_proxy_to(target) *)
  | CreateCopyOf        (* create_copy_of(target) *)
  | CreateFromBlueprint bool (* raw_args; code_offset is an evaluated operand *)
                        (* create_from_blueprint(target, *args) *)
  | RawCreate           (* raw_create(bytecode, *args) *)
End

Datatype:
  call_target
  = IntCall nsid
  | ExtCall bool bool ext_call_sig (* is_static, skip_contract_check, resolved signature *)
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
  (* raw_call(to, msg.data, ...): original transaction input, never a bounded
     ordinary expression. Runtime operands are [to_addr; value]. *)
  | RawCallCalldataTarget raw_call_flags
  (* raw_log(topics, data)
     args = [data_bytes; topic1; ...; topicN] where N ≤ 4 *)
  | RawLog
  (* raw_revert(data) — terminus
     args = [data_bytes] *)
  | RawRevert
  (* selfdestruct(to) — terminus
     args = [to_addr] *)
  | SelfDestructTarget
  (* Creation operands are stored in their runtime evaluation order:
     - minimal proxy/copy: [target; value] ++ [salt]?
     - blueprint: [target; value] ++ [salt]? ++ [code_offset] ++ ctor_args
     - raw_create: [bytecode; value] ++ ctor_args ++ [salt]?
     The first bool records salt presence; the second is revert_on_failure. *)
  | CreateTarget create_kind bool (* has_salt *) bool (* revert_on_failure *)
End

Datatype:
  type_builtin = Empty | MaxValue | MinValue | Epsilon | Convert | Extract32
  | AbiDecode bool (* unwrap_tuple *)
  | AbiEncode bool (word8 list option) (* ensure_tuple, optional 4-byte method ID *)
End

Definition abi_encode_method_id_bytes_def:
  abi_encode_method_id_bytes NONE = [] /\
  abi_encode_method_id_bytes (SOME bs) = bs
End

val () = cv_auto_trans abi_encode_method_id_bytes_def;

Datatype:
  expr
  = Name type identifier              (* local/scoped variable *)
  | TopLevelName type nsid            (* top-level binding: self.x, module.x, constants/immutables *)
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
  | TopLevelNameTarget nsid            (* top-level binding target *)
  | SubscriptTarget base_assignment_target expr
  | AttributeTarget base_assignment_target identifier
End

(* A resolved custom-error use retains positional and keyword operands separately.
   The declaration determines keyword order and the canonical ABI types. *)
Datatype:
  custom_error
  = CustomError nsid (expr list) ((identifier # expr) list)
End


Definition expr_type_def:
  (expr_type (Name ty _) = ty) /\
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
  | AssertCustomError custom_error
End

Datatype:
  raise_reason
  = RaiseBare                 (* bare raise: revert 0,0 *)
  | RaiseUnreachable          (* raise UNREACHABLE → INVALID opcode *)
  | RaiseReason expr          (* raise with Error(string) reason *)
  | RaiseCustomError custom_error
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
      bool (* raw_return: @raw_return decorator, bypass ABI encoding *)
      identifier (argument list) (expr list) type (stmt list)
  | VariableDecl variable_visibility variable_mutability identifier type (num option) (* storage/transient slot *)
  | HashMapDecl variable_visibility bool (* transient? *) identifier type value_type (num option) (* slot *)
  | StructDecl identifier (argument list)
  | EventDecl identifier ((argument # bool) list)  (* bool = indexed *)
  | ErrorDecl identifier (argument list)
  | FlagDecl identifier (identifier list)
  | InterfaceDecl identifier (interface_func list)
End

(* Consume keyword arguments in declaration order.  Removing each match makes
   duplicates, omissions, and unknown names fail instead of being ignored. *)
Definition take_custom_error_kwarg_def:
  take_custom_error_kwarg name [] = NONE ∧
  take_custom_error_kwarg name ((key,e)::rest) =
    if key = name then SOME (e,rest)
    else
      case take_custom_error_kwarg name rest of
      | NONE => NONE
      | SOME (found,rest') => SOME (found,(key,e)::rest')
End

Definition order_custom_error_kwargs_def:
  order_custom_error_kwargs [] kwargs =
    (if NULL kwargs then SOME [] else NONE) ∧
  order_custom_error_kwargs ((name,ty)::params) kwargs =
    case take_custom_error_kwarg name kwargs of
    | NONE => NONE
    | SOME (e,kwargs') =>
        OPTION_MAP (CONS e) (order_custom_error_kwargs params kwargs')
End

Definition custom_error_exprs_def:
  custom_error_exprs (CustomError id positional kwargs) =
    positional ++ MAP SND kwargs
End

Theorem take_custom_error_kwarg_perm:
  take_custom_error_kwarg name kwargs = SOME (e,rest) ⇒
  PERM (MAP SND kwargs) (e::MAP SND rest)
Proof
  qid_spec_tac `rest` >>
  qid_spec_tac `e` >>
  qid_spec_tac `name` >>
  Induct_on `kwargs` >- simp[take_custom_error_kwarg_def] >>
  Cases_on `h` >>
  rw[take_custom_error_kwarg_def] >>
  gvs[AllCaseEqs(), PERM_CONS_IFF] >>
  irule PERM_TRANS >>
  qexists_tac `r::e::MAP SND rest'` >>
  conj_tac
  >- (qpat_x_assum `∀name e rest. _`
        (qspecl_then [`name`, `e`, `rest'`] mp_tac) >>
      simp[]) >>
  simp[PERM_SWAP_AT_FRONT]
QED

Theorem order_custom_error_kwargs_perm:
  order_custom_error_kwargs params kwargs = SOME es ⇒
  PERM (MAP SND kwargs) es
Proof
  qid_spec_tac `es` >>
  qid_spec_tac `kwargs` >>
  Induct_on `params`
  >- (Cases_on `kwargs` >> simp[order_custom_error_kwargs_def]) >>
  Cases_on `h` >>
  rw[order_custom_error_kwargs_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  drule_all take_custom_error_kwarg_perm >>
  strip_tac >>
  irule PERM_TRANS >>
  qexists_tac `e::MAP SND kwargs'` >>
  simp[PERM_CONS_IFF]
QED

Theorem list_size_append_custom:
  ∀f xs ys. list_size f (xs ++ ys) = list_size f xs + list_size f ys
Proof
  Induct_on `xs` >> simp[listTheory.list_size_def]
QED


Theorem list_size_map_snd_le:
  ∀kwargs : (identifier # expr) list.
    list_size (λx. expr_size (SND x)) kwargs ≤
    list_size (pair_size (list_size char_size) expr_size) kwargs
Proof
  Induct_on `kwargs` >- simp[] >>
  Cases_on `h` >> fs[]
QED

Theorem custom_error_exprs_size[simp]:
  list_size expr_size (custom_error_exprs err) < custom_error_size err + 2
Proof
  Cases_on `err` >>
  simp[custom_error_exprs_def, list_size_append_custom] >>
  irule LESS_EQ_LESS_TRANS >>
  qexists_tac
    `list_size (pair_size (list_size char_size) expr_size) l0` >>
  simp[list_size_map_snd_le]
QED
Theorem custom_error_exprs_size_with_expr[simp]:
  list_size expr_size (custom_error_exprs err) <
    custom_error_size err + (expr_size e + 2)
Proof
  irule LESS_LESS_EQ_TRANS >>
  qexists_tac `custom_error_size err + 2` >>
  simp[]
QED



Definition order_custom_error_args_def:
  order_custom_error_args params (CustomError id positional kwargs) =
    if NULL kwargs then
      if LENGTH positional = LENGTH params then SOME positional else NONE
    else if NULL positional then order_custom_error_kwargs params kwargs
    else NONE
End
Theorem order_custom_error_args_perm:
  order_custom_error_args params err = SOME es ⇒
  PERM (custom_error_exprs err) es
Proof
  Cases_on `err` >>
  Cases_on `l` >>
  Cases_on `l0`
  >- simp[order_custom_error_args_def, custom_error_exprs_def]
  >- (rw[order_custom_error_args_def, custom_error_exprs_def] >>
      drule order_custom_error_kwargs_perm >> simp[])
  >- simp[order_custom_error_args_def, custom_error_exprs_def]
  >- simp[order_custom_error_args_def, custom_error_exprs_def]
QED

val () = cv_auto_trans take_custom_error_kwarg_def;
val () = cv_auto_trans custom_error_exprs_def;

val order_custom_error_kwargs_pre_def =
  cv_auto_trans_pre "order_custom_error_kwargs_pre"
                    order_custom_error_kwargs_def;

Theorem order_custom_error_kwargs_pre[cv_pre]:
  ∀params kwargs. order_custom_error_kwargs_pre params kwargs
Proof
  ho_match_mp_tac order_custom_error_kwargs_ind >> rw[] >>
  rw[Once order_custom_error_kwargs_pre_def]
QED

val () = cv_auto_trans order_custom_error_args_def;

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
