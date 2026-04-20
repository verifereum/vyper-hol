Theory vyperTypeSoundnessDefs
Ancestors
  list rich_list pred_set prim_rec sorting relation arithmetic
  finite_map combin option pair byte
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage
  vyperStatePreservation vyperScopePreservation vyperStorageBackend
  vyperLookup vyperImmutablesPreservation
  vyperEvalExprPreservesScopesDom
  vyperEvalPreservesScopes vyperEvalPreservesImmutablesDom
  vyperTyping vyperEncodeDecode vyperAssignPreservesType vyperArith
Libs
  wordsLib


Definition is_int_type_def[simp]:
  is_int_type (BaseT (UintT _)) = T /\
  is_int_type (BaseT (IntT _)) = T /\
  is_int_type _ = F
End

Definition is_numeric_type_def[simp]:
  is_numeric_type t = (is_int_type t \/ t = BaseT DecimalT)
End

Definition is_bool_type_def[simp]:
  is_bool_type (BaseT BoolT) = T /\
  is_bool_type _ = F
End

Definition is_flag_type_def[simp]:
  is_flag_type (FlagT _) = T /\
  is_flag_type _ = F
End

Definition is_struct_type_def[simp]:
  is_struct_type (StructT _) = T /\
  is_struct_type _ = F
End

Definition is_sized_type_def[simp]:
  is_sized_type (ArrayT _ _) = T /\
  is_sized_type (BaseT (StringT _)) = T /\
  is_sized_type (BaseT (BytesT _)) = T /\
  is_sized_type _ = F
End


(* ===== well_typed_literal ===== *)

Definition well_typed_literal_def:
  well_typed_literal (BaseT BoolT) (BoolL _) = T /\
  well_typed_literal (BaseT (UintT k)) (IntL n) =
    (within_int_bound (Unsigned k) n /\ k ≤ 256) /\
  well_typed_literal (BaseT (IntT k)) (IntL n) =
    (within_int_bound (Signed k) n /\ k ≤ 256) /\
  well_typed_literal (BaseT DecimalT) (DecimalL n) =
    within_int_bound (Signed 168) n /\
  well_typed_literal (BaseT (StringT n)) (StringL s) =
    (LENGTH s <= n) /\
  well_typed_literal (BaseT (BytesT bd)) (BytesL bs) =
    (compatible_bound bd (LENGTH bs) /\
     case bd of Fixed n => n ≤ 32 | _ => T) /\
  well_typed_literal _ _ = F
End

(* ===== Binary operation typing ===== *)

Definition well_typed_binop_def:
  (* Arithmetic: operands and result same numeric type *)
  well_typed_binop ty Add t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Sub t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Mul t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Div t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Mod t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Exp t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty ExpMod t1 t2 =
    (t1 = ty /\ t2 = ty /\ ty = BaseT (UintT 256)) /\
  (* Wrapping arithmetic: int types only *)
  well_typed_binop ty UAdd t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty USub t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty UMul t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty UDiv t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  (* Shifts: result same as first operand, both int *)
  well_typed_binop ty ShL t1 t2 =
    (t1 = ty /\ is_int_type ty /\ is_int_type t2) /\
  well_typed_binop ty ShR t1 t2 =
    (t1 = ty /\ is_int_type ty /\ is_int_type t2) /\
  (* Bitwise: int, bool, or flag *)
  well_typed_binop ty And t1 t2 =
    (t1 = ty /\ t2 = ty /\
     (is_int_type ty \/ is_bool_type ty \/ is_flag_type ty)) /\
  well_typed_binop ty Or t1 t2 =
    (t1 = ty /\ t2 = ty /\
     (is_int_type ty \/ is_bool_type ty \/ is_flag_type ty)) /\
  well_typed_binop ty XOr t1 t2 =
    (t1 = ty /\ t2 = ty /\
     (is_int_type ty \/ is_bool_type ty \/ is_flag_type ty)) /\
  (* Comparison: same-typed operands, result is bool *)
  well_typed_binop ty Eq t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT) /\
  well_typed_binop ty NotEq t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT) /\
  well_typed_binop ty Lt t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty LtE t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty Gt t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty GtE t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  (* Min/Max: same numeric type *)
  well_typed_binop ty Min t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Max t1 t2 =
    (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  (* Membership: result is bool, element type matches array element type *)
  well_typed_binop ty In t1 t2 =
    (ty = BaseT BoolT /\ ?bd. t2 = ArrayT t1 bd) /\
  well_typed_binop ty NotIn t1 t2 =
    (ty = BaseT BoolT /\ ?bd. t2 = ArrayT t1 bd)
End

(* ===== Environment item types ===== *)

Definition env_item_type_def:
  env_item_type Sender = BaseT AddressT /\
  env_item_type SelfAddr = BaseT AddressT /\
  env_item_type ValueSent = BaseT (UintT 256) /\
  env_item_type TimeStamp = BaseT (UintT 256) /\
  env_item_type BlockNumber = BaseT (UintT 256) /\
  env_item_type BlobBaseFee = BaseT (UintT 256) /\
  env_item_type GasPrice = BaseT (UintT 256) /\
  env_item_type PrevHash = BaseT (BytesT (Fixed 32)) /\
  env_item_type ChainId = BaseT (UintT 256) /\
  env_item_type Coinbase = BaseT AddressT /\
  env_item_type GasLimit = BaseT (UintT 256) /\
  env_item_type BaseFee = BaseT (UintT 256) /\
  env_item_type PrevRandao = BaseT (UintT 256) /\
  env_item_type TxOrigin = BaseT AddressT /\
  env_item_type MsgGas = BaseT (UintT 256)
End

Definition account_item_type_def:
  account_item_type Address = BaseT AddressT /\
  account_item_type Balance = BaseT (UintT 256) /\
  account_item_type Codehash = BaseT (BytesT (Fixed 32)) /\
  account_item_type Codesize = BaseT (UintT 256) /\
  account_item_type IsContract = BaseT BoolT /\
  account_item_type Code = BaseT (BytesT (Dynamic 24576))
End

(* ===== Builtin application typing ===== *)

Definition well_typed_builtin_app_def:
  (* Binary operations *)
  well_typed_builtin_app ty (Bop bop) ts =
    (LENGTH ts = 2 /\
     well_typed_binop ty bop (EL 0 ts) (EL 1 ts)) /\
  (* Len: array/string/bytes -> uint256 *)
  well_typed_builtin_app ty Len ts =
    (LENGTH ts = 1 /\ ty = BaseT (UintT 256) /\
     is_sized_type (HD ts)) /\
  (* Not: bool/int/flag -> same type *)
  well_typed_builtin_app ty Not ts =
    (LENGTH ts = 1 /\ HD ts = ty /\
     (is_bool_type ty \/ is_int_type ty \/ is_flag_type ty)) /\
  (* Neg: numeric -> same type *)
  well_typed_builtin_app ty Neg ts =
    (ts = [ty] /\ is_numeric_type ty) /\
  (* Keccak256: bytes/string -> bytes32 *)
  well_typed_builtin_app ty Keccak256 ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32)) /\ is_sized_type (HD ts)) /\
  (* AsWeiValue: numeric -> uint256 *)
  well_typed_builtin_app ty (AsWeiValue _) ts =
    (LENGTH ts = 1 /\ ty = BaseT (UintT 256) /\ is_numeric_type (HD ts)) /\
  (* Concat: 2+ bytes/string args -> bytes/string.
     Argument types must be consistent with result type:
     all BytesT for bytes result, all StringT for string result. *)
  well_typed_builtin_app ty (Concat n) ts =
    (2 <= LENGTH ts /\
     ((ty = BaseT (BytesT (Dynamic n)) /\
       EVERY (\t. ?bd. t = BaseT (BytesT bd)) ts) \/
      (ty = BaseT (StringT n) /\
       EVERY (\t. ?m. t = BaseT (StringT m)) ts))) /\
  (* Slice: source, start, length -> bytes/string.
     First arg type must be consistent with result type. *)
  well_typed_builtin_app ty (Slice n) ts =
    (LENGTH ts = 3 /\
     is_int_type (EL 1 ts) /\ is_int_type (EL 2 ts) /\
     ((ty = BaseT (BytesT (Dynamic n)) /\
       ?bd. HD ts = BaseT (BytesT bd)) \/
      (ty = BaseT (StringT n) /\
       ?m. HD ts = BaseT (StringT m)))) /\
  (* Uint2Str: uint -> string *)
  well_typed_builtin_app ty (Uint2Str n) ts =
    (LENGTH ts = 1 /\ ty = BaseT (StringT n) /\
     is_int_type (HD ts) /\ 78 <= n) /\
  (* MakeArray: disabled — for NONE case, TupleT component types are
     not connected to argument types in the current typing scheme.
     For SOME case, all elements must have the same type but
     well_typed_builtin_app doesn't constrain this. *)
  well_typed_builtin_app ty (MakeArray type_opt bd) ts = F /\
  (* Ceil/Floor: decimal -> int256 (Vyper: floor/ceil always return int256) *)
  well_typed_builtin_app ty Ceil ts =
    (LENGTH ts = 1 /\ HD ts = BaseT DecimalT /\
     ty = BaseT (IntT 256)) /\
  well_typed_builtin_app ty Floor ts =
    (LENGTH ts = 1 /\ HD ts = BaseT DecimalT /\
     ty = BaseT (IntT 256)) /\
  (* AddMod/MulMod: 3x uint256 -> uint256 *)
  well_typed_builtin_app ty AddMod ts =
    (LENGTH ts = 3 /\ ty = BaseT (UintT 256) /\
     EVERY ((=) (BaseT (UintT 256))) ts) /\
  well_typed_builtin_app ty MulMod ts =
    (LENGTH ts = 3 /\ ty = BaseT (UintT 256) /\
     EVERY ((=) (BaseT (UintT 256))) ts) /\
  (* BlockHash/BlobHash: uint256 -> bytes32 *)
  well_typed_builtin_app ty BlockHash ts =
    (ts = [BaseT (UintT 256)] /\
     ty = BaseT (BytesT (Fixed 32))) /\
  well_typed_builtin_app ty BlobHash ts =
    (ts = [BaseT (UintT 256)] /\
     ty = BaseT (BytesT (Fixed 32))) /\
  (* Env: no args, return type depends on item *)
  well_typed_builtin_app ty (Env item) ts =
    (ts = [] /\ ty = env_item_type item) /\
  (* Acc: disabled — account fields (balance, code length) are unbounded
     in the HOL model. Proving typing would require threading an
     accounts_well_typed invariant through all 56 induction cases.
     See LEARNINGS for details. *)
  well_typed_builtin_app ty (Acc item) ts = F /\
  (* Isqrt: uint256 -> uint256 *)
  well_typed_builtin_app ty Isqrt ts =
    (ts = [BaseT (UintT 256)] /\
     ty = BaseT (UintT 256)) /\
  (* MethodId: string/bytes -> bytes4 *)
  well_typed_builtin_app ty MethodId ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 4))) /\
  (* EC operations — first arg is bytes32, rest are int or bytes *)
  well_typed_builtin_app ty ECRecover ts =
    (LENGTH ts = 4 /\ ty = BaseT AddressT /\
     HD ts = BaseT (BytesT (Fixed 32)) /\
     EVERY (\t. is_int_type t \/ ?bd. t = BaseT (BytesT bd)) (TL ts)) /\
  well_typed_builtin_app ty ECAdd ts =
    (LENGTH ts = 2 /\ ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EVERY (\t. t = ArrayT (BaseT (UintT 256)) (Fixed 2)) ts) /\
  well_typed_builtin_app ty ECMul ts =
    (LENGTH ts = 2 /\ ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EVERY (\t. t = ArrayT (BaseT (UintT 256)) (Fixed 2)) ts) /\
  (* PowMod256: 2x uint256 -> uint256 *)
  well_typed_builtin_app ty PowMod256 ts =
    (ts = [BaseT (UintT 256); BaseT (UintT 256)] /\
     ty = BaseT (UintT 256)) /\
  (* Abs: numeric -> same type *)
  well_typed_builtin_app ty Abs ts =
    (ts = [ty] /\ is_numeric_type ty) /\
  (* Sha256: bytes/string -> bytes32 *)
  well_typed_builtin_app ty Sha256 ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32)) /\ is_sized_type (HD ts))
End

(* ===== Type well-formedness ===== *)

Definition well_formed_type_def:
  well_formed_type tenv ty = IS_SOME (evaluate_type tenv ty)
End

(* ===== Subscript typing ===== *)

Definition subscript_type_ok_def:
  subscript_type_ok (ArrayT elem_ty _) idx_ty result_ty =
    (result_ty = elem_ty /\ is_int_type idx_ty) /\
  subscript_type_ok (TupleT ts) idx_ty result_ty =
    (is_int_type idx_ty /\ ts <> [] /\ EVERY ($= result_ty) ts) /\
  subscript_type_ok _ _ _ = F
End

(* ===== Attribute typing ===== *)

(* Check struct has field with expected type *)
Definition attribute_type_ok_def:
  attribute_type_ok tenv (StructT sname) field_id result_ty =
    (case FLOOKUP tenv (string_to_num sname) of
       SOME (StructArgs fields) =>
         (case ALOOKUP fields field_id of
            SOME field_ty => result_ty = field_ty
          | NONE => F)
     | _ => F) /\
  attribute_type_ok _ _ _ _ = F
End

(* ===== Runtime type invariant ===== *)
(*
 * The runtime already stores (type_value # value) pairs in scopes and
 * immutables. state_well_typed asserts that every such pair is consistent:
 * the value actually satisfies its associated type_value.
 *
 * This is a runtime invariant — no ghost typing environment needed.
 *)

Definition scope_well_typed_def:
  scope_well_typed (sc : scope) ⇔
    ∀id entry. FLOOKUP sc id = SOME entry ⇒
      value_has_type entry.type entry.value ∧ well_formed_type_value entry.type
End

Definition imms_well_typed_def:
  imms_well_typed (imms : module_immutables) ⇔
    ∀src_id_opt m id tv v.
      ALOOKUP imms src_id_opt = SOME m ∧
      FLOOKUP m id = SOME (tv, v) ⇒
      value_has_type tv v ∧ well_formed_type_value tv
End

Definition state_well_typed_def:
  state_well_typed st ⇔
    EVERY scope_well_typed st.scopes ∧
    EVERY (λ(addr, mods). imms_well_typed mods) st.immutables
End

Datatype:
  typing_env = <|
    var_types : (num |-> type);
    global_types : (num |-> type);
    toplevel_types : ((num option # num) |-> type);
    type_defs : (num |-> type_args);
    fn_sigs : ((num option # string) |-> (type list # type));
    flag_members : ((num option # string) |-> string list);
  |>
End

(* fn_sigs_consistent: for any function signature in fn_sigs,
   the runtime lookup agrees *)
Definition fn_sigs_consistent_def:
  fn_sigs_consistent fn_sigs cx <=>
    !src_id_opt fn param_types ret_ty.
      FLOOKUP fn_sigs (src_id_opt, fn) = SOME (param_types, ret_ty) ==>
      ?ts fm nr params dflts body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts =
          SOME (fm, nr, params, dflts, ret_ty, body) /\
        param_types = MAP SND params
End

(* env_consistent: typing env matches runtime state *)
Definition env_consistent_def:
  env_consistent env cx st <=>
    env.type_defs = get_tenv cx /\
    fn_sigs_consistent env.fn_sigs cx /\
    (!id ty entry.
       FLOOKUP env.var_types id = SOME ty /\
       lookup_scopes id st.scopes = SOME entry ==>
       evaluate_type (get_tenv cx) ty = SOME entry.type) /\
    (!id ty tv v.
       FLOOKUP env.global_types id = SOME ty /\
       FLOOKUP (get_source_immutables (current_module cx)
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (* toplevel_types: declared type in module code matches typing env *)
    (!src_id_opt id ty ts.
       FLOOKUP env.toplevel_types (src_id_opt, id) = SOME ty /\
       get_module_code cx src_id_opt = SOME ts ==>
       (* StorageVarDecl: declared type matches *)
       (!is_transient typ id_str.
          find_var_decl_by_num id ts =
            SOME (StorageVarDecl is_transient typ, id_str) ==>
          typ = ty) /\
       (* HashMapVarDecl: type is NoneT *)
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts =
            SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
          ty = NoneT) /\
       (* Immutable: stored type_value matches *)
       (find_var_decl_by_num id ts = NONE ==>
         !tv v. FLOOKUP (get_source_immutables src_id_opt
           (case ALOOKUP st.immutables cx.txn.target of
              SOME m => m | NONE => [])) id = SOME (tv, v) ==>
         evaluate_type (get_tenv cx) ty = SOME tv)) /\
    (* Flag member consistency: flag_members map agrees with module code *)
    (!src_id_opt fid ls.
       FLOOKUP env.flag_members (src_id_opt, fid) = SOME ls ==>
       ?ts. get_module_code cx src_id_opt = SOME ts /\
            lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) =
              SOME (FlagArgs (LENGTH ls)))
End

(* ===== well_typed_expr: state-independent AST annotation consistency ===== *)

(* Return type of raw_call depends on flags *)
Definition raw_call_return_type_def:
  raw_call_return_type flags =
    if flags.rcf_revert_on_failure then
      if flags.rcf_max_outsize = 0 then NoneT
      else BaseT (BytesT (Dynamic flags.rcf_max_outsize))
    else
      if flags.rcf_max_outsize = 0 then BaseT BoolT
      else TupleT [BaseT BoolT; BaseT (BytesT (Dynamic flags.rcf_max_outsize))]
End

Definition well_typed_expr_def:
  well_typed_expr env (Name ty id) =
    (FLOOKUP env.var_types (string_to_num id) = SOME ty) /\
  well_typed_expr env (BareGlobalName ty id) =
    (FLOOKUP env.global_types (string_to_num id) = SOME ty) /\
  (* ty <> NoneT excludes HashMaps: HashMapVarDecl has type NoneT in
     toplevel_types, but HashMaps are not first-class values — they can
     only be accessed via subscripting. materialise(HashMapRef) raises
     TypeError, so well-typed programs must not use them as values. *)
  well_typed_expr env (TopLevelName ty (src_id_opt, id)) =
    (FLOOKUP env.toplevel_types (src_id_opt, string_to_num id) = SOME ty /\
     well_formed_type env.type_defs ty /\
     ty <> NoneT) /\
  well_typed_expr env (FlagMember ty (src_id_opt, fid) mid) =
    (ty = FlagT fid /\
     well_formed_type env.type_defs ty /\
     ?ls. FLOOKUP env.flag_members (src_id_opt, fid) = SOME ls /\
          MEM mid ls) /\
  well_typed_expr env (IfExp ty cond e1 e2) =
    (well_typed_expr env cond /\
     well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     expr_type cond = BaseT BoolT /\
     expr_type e1 = ty /\ expr_type e2 = ty) /\
  well_typed_expr env (Literal ty l) =
    (well_typed_literal ty l /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (StructLit ty _ kes) =
    (well_typed_named_exprs env kes /\
     is_struct_type ty /\
     well_formed_type env.type_defs ty /\
     ?id args. ty = StructT id /\
            FLOOKUP env.type_defs (string_to_num id) = SOME (StructArgs args) /\
            MAP FST kes = MAP FST args /\
            MAP (expr_type o SND) kes = MAP SND args) /\
  well_typed_expr env (Subscript ty e1 e2) =
    (well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     subscript_type_ok (expr_type e1) (expr_type e2) ty) /\
  well_typed_expr env (Attribute ty e id) =
    (well_typed_expr env e /\
     attribute_type_ok env.type_defs (expr_type e) id ty) /\
  well_typed_expr env (Builtin ty blt es) =
    (well_typed_exprs env es /\
     well_typed_builtin_app ty blt (MAP expr_type es) /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (TypeBuiltin ty tb target_ty es) =
    (well_typed_exprs env es /\
     ty = target_ty /\
     (!b. tb <> AbiEncode b) /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Pop ty tgt) =
    (?bd. well_typed_target env tgt (ArrayT ty bd)) /\
  well_typed_expr env (Call ty (IntCall (src_id_opt, fn_name)) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     well_formed_type env.type_defs ty /\
     ?param_types ret_ty.
       FLOOKUP env.fn_sigs (src_id_opt, fn_name) = SOME (param_types, ret_ty) /\
       ty = ret_ty /\
       MAP expr_type args = TAKE (LENGTH args) param_types) /\
  well_typed_expr env (Call ty (ExtCall _ (_, arg_types, ret_ty)) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     well_formed_type env.type_defs ty /\
     ty = ret_ty /\
     MAP expr_type args = arg_types /\
     (!e. drv = SOME e ==> expr_type e = ret_ty)) /\
  well_typed_expr env (Call ty Send args drv) =
    (well_typed_exprs env args /\
     LENGTH args = 2 /\ ty = NoneT /\
     HD (MAP expr_type args) = BaseT AddressT /\
     is_int_type (EL 1 (MAP expr_type args))) /\
  (* Chain interaction builtins — constrained return types *)
  well_typed_expr env (Call ty (RawCallTarget flags) args drv) =
    (well_typed_exprs env args /\
     ty = raw_call_return_type flags /\
     flags.rcf_max_outsize < dimword(:256) /\
     LENGTH args = 3 /\
     EL 0 (MAP expr_type args) = BaseT AddressT /\
     ?bd. EL 1 (MAP expr_type args) = BaseT (BytesT bd) /\
     is_int_type (EL 2 (MAP expr_type args))) /\
  well_typed_expr env (Call ty RawLog args drv) =
    (well_typed_exprs env args /\
     ty = NoneT /\
     LENGTH args = 2 /\
     ?bd. EL 0 (MAP expr_type args) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
     ?bd'. EL 1 (MAP expr_type args) = BaseT (BytesT bd')) /\
  well_typed_expr env (Call ty RawRevert args drv) =
    (well_typed_exprs env args /\
     LENGTH args = 1 /\
     ?bd. HD (MAP expr_type args) = BaseT (BytesT bd)) /\
  well_typed_expr env (Call ty SelfDestructTarget args drv) =
    (well_typed_exprs env args /\
     ty = NoneT /\
     LENGTH args = 1 /\
     HD (MAP expr_type args) = BaseT AddressT) /\
  well_typed_expr env (Call ty (CreateTarget kind rof) args drv) =
    (well_typed_exprs env args /\
     ty = BaseT AddressT /\
     LENGTH args >= 2 /\
     HD (MAP expr_type args) = BaseT AddressT /\
     is_int_type (LAST (MAP expr_type args))) /\
  well_typed_target env (NameTarget id) ty =
    (FLOOKUP env.var_types (string_to_num id) = SOME ty) /\
  well_typed_target env (BareGlobalNameTarget id) ty =
    (FLOOKUP env.global_types (string_to_num id) = SOME ty) /\
  well_typed_target env (TopLevelNameTarget (src_id_opt, id)) ty =
    (FLOOKUP env.toplevel_types (src_id_opt, string_to_num id) = SOME ty) /\
  well_typed_target env (SubscriptTarget tgt e) ty =
    (?tgt_ty. well_typed_target env tgt tgt_ty /\
     well_typed_expr env e /\
     subscript_type_ok tgt_ty (expr_type e) ty /\
     ~is_TupleT tgt_ty) /\
  well_typed_target env (AttributeTarget tgt id) ty =
    (?tgt_ty. well_typed_target env tgt tgt_ty /\
     attribute_type_ok env.type_defs tgt_ty id ty) /\
  well_typed_exprs env [] = T /\
  well_typed_exprs env (e::es) =
    (well_typed_expr env e /\ well_typed_exprs env es) /\
  well_typed_opt env NONE = T /\
  well_typed_opt env (SOME e) = well_typed_expr env e /\
  well_typed_named_exprs env [] = T /\
  well_typed_named_exprs env ((k,e)::kes) =
    (well_typed_expr env e /\ well_typed_named_exprs env kes)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (_, e) => expr_size e
    | INR (INL (_, tgt, _)) => base_assignment_target_size tgt
    | INR (INR (INL (_, es))) => expr4_size es
    | INR (INR (INR (INL (_, opt)))) => expr3_size opt
    | INR (INR (INR (INR (_, kes)))) => expr1_size kes)`
  \\ simp[expr_size_def]
  \\ qsuff_tac
       `(!es. expr4_size es = list_size expr_size es) /\
        (!drv. expr3_size drv = option_size expr_size drv) /\
        (!kes. expr1_size kes =
               list_size (pair_size (list_size char_size) expr_size) kes)`
  >- (strip_tac \\ asm_rewrite_tac[] \\ DECIDE_TAC)
  \\ rpt conj_tac
  \\ TRY (Induct \\ simp[expr_size_def, listTheory.list_size_def,
            basicSizeTheory.pair_size_def])
  \\ Cases
  \\ simp[expr_size_def, basicSizeTheory.option_size_def]
End

(* ===== well_typed_stmt: static typing for statements ===== *)

(* well_typed for assignment targets (base + tuple) *)
Definition well_typed_atarget_def:
  well_typed_atarget env (BaseTarget bt) ty =
    well_typed_target env bt ty /\
  well_typed_atarget env (TupleTarget tgts) ty =
    (?tys. LIST_REL (\tgt ty. well_typed_atarget env tgt ty) tgts tys /\
           ty = TupleT tys)
Termination
  WF_REL_TAC`measure (λ(_,t,_). assignment_target_size t)`
End

Definition well_typed_iterator_def:
  well_typed_iterator env typ (Array e) =
    (well_typed_expr env e /\
     ?bd. expr_type e = ArrayT typ bd) /\
  well_typed_iterator env typ (Range e1 e2) =
    (well_typed_expr env e1 /\ well_typed_expr env e2 /\
     is_int_type typ /\ expr_type e1 = typ /\ expr_type e2 = typ)
End

Definition well_typed_stmt_def:
  well_typed_stmt env ret_ty Pass = T /\
  well_typed_stmt env ret_ty Continue = T /\
  well_typed_stmt env ret_ty Break = T /\
  well_typed_stmt env ret_ty (Expr e) =
    well_typed_expr env e /\
  well_typed_stmt env ret_ty (Return NONE) =
    (ret_ty = NoneT) /\
  well_typed_stmt env ret_ty (Return (SOME e)) =
    (well_typed_expr env e /\ expr_type e = ret_ty) /\
  well_typed_stmt env ret_ty (Raise RaiseBare) = T /\
  well_typed_stmt env ret_ty (Raise RaiseUnreachable) = T /\
  well_typed_stmt env ret_ty (Raise (RaiseReason e)) =
    well_typed_expr env e /\
  well_typed_stmt env ret_ty (Assert e AssertBare) =
    (well_typed_expr env e /\
     expr_type e = BaseT BoolT) /\
  well_typed_stmt env ret_ty (Assert e AssertUnreachable) =
    (well_typed_expr env e /\
     expr_type e = BaseT BoolT) /\
  well_typed_stmt env ret_ty (Assert e (AssertReason se)) =
    (well_typed_expr env e /\
     well_typed_expr env se /\
     expr_type e = BaseT BoolT /\
     ?n. expr_type se = BaseT (StringT n)) /\
  well_typed_stmt env ret_ty (Log id es) =
    well_typed_exprs env es /\
  well_typed_stmt env ret_ty (AnnAssign id typ e) =
    (well_typed_expr env e /\
     well_formed_type env.type_defs typ /\
     expr_type e = typ /\
     string_to_num id NOTIN FDOM env.var_types) /\
  well_typed_stmt env ret_ty (Append bt e) =
    (?arr_ty elem_ty bd.
     arr_ty = ArrayT elem_ty bd /\
     well_typed_target env bt arr_ty /\
     well_typed_expr env e /\
     expr_type e = elem_ty) /\
  well_typed_stmt env ret_ty (Assign tgt e) =
    (well_typed_atarget env tgt (expr_type e) /\
     well_typed_expr env e) /\
  well_typed_stmt env ret_ty (AugAssign ty bt bop e) =
    (well_typed_target env bt ty /\
     well_typed_expr env e /\
     well_formed_type env.type_defs ty /\
     well_typed_binop ty bop ty (expr_type e)) /\
  well_typed_stmt env ret_ty (If e ss1 ss2) =
    (well_typed_expr env e /\
     expr_type e = BaseT BoolT /\
     well_typed_stmts env ret_ty ss1 /\
     well_typed_stmts env ret_ty ss2) /\
  well_typed_stmt env ret_ty (For id typ it n body) =
    (well_formed_type env.type_defs typ /\
     well_typed_iterator env typ it /\
     string_to_num id NOTIN FDOM env.var_types /\
     well_typed_stmts
       (env with var_types updated_by (flip FUPDATE (string_to_num id, typ)))
       ret_ty body) /\
  well_typed_stmts env ret_ty [] = T /\
  well_typed_stmts env ret_ty (s::ss) =
    (well_typed_stmt env ret_ty s /\
     well_typed_stmts env ret_ty ss)
Termination
  WF_REL_TAC`measure (λx.
    case x of INL(_,_,t) => stmt_size t
            | INR(_,_,ts) => list_size stmt_size ts)`
End

(* ===== functions_well_typed: all callable functions are well-typed ===== *)
(* functions_well_typed: global invariant about callable functions.
 * For every callable function:
 *   - body is well-typed under some env_body
 *   - defaults are well-typed in a minimal env (no local var refs)
 *   - parameters are tracked in env_body.var_types
 *   - return type evaluates successfully
 * Also: the call site's type annotation must match (safe_cast will
 * only produce a satisfies_type result if types match).
 *)
(* functions_well_typed cx:
 *   For every callable function in the program:
 *   1. There exists a typing env env_body with matching type_defs
 *   2. The return type evaluates to some ret_tv
 *   3. The function body is well-typed under env_body
 *   4. Default values are well-typed (in a minimal env with no local vars)
 *   5. Each parameter is in env_body.var_types
 *   6. env_body.toplevel_types match storage declarations (type matches decl,
 *      and evaluate_type is defined = immutable type annotations are well-formed)
 *   7. env_body.flag_members match module flag declarations
 *
 *   The call site's type annotation ty must match the function's declared
 *   return type ret — this is ensured by the Vyper compiler frontend.
 *)
Definition functions_well_typed_def:
  functions_well_typed cx <=>
    !src_id_opt fn ts fm nr args dflts ret body fn_sigs.
      get_module_code cx src_id_opt = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts =
        SOME (fm, nr, args, dflts, ret, body) /\
      fn_sigs_consistent fn_sigs cx ==>
      (nr ==> cx.nonreentrant_slot <> NONE) /\
      ?env_body ret_tv.
        env_body.type_defs = get_tenv cx /\
        env_body.fn_sigs = fn_sigs /\
        env_body.global_types = FEMPTY /\
        (* toplevel_types: match storage decls + immutable type consistency *)
        (!src id ty ts'.
           FLOOKUP env_body.toplevel_types (src, id) = SOME ty /\
           get_module_code cx src = SOME ts' ==>
           (!is_transient typ id_str.
              find_var_decl_by_num id ts' =
                SOME (StorageVarDecl is_transient typ, id_str) ==>
              typ = ty) /\
           (!is_transient kt vt id_str.
              find_var_decl_by_num id ts' =
                SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
              ty = NoneT) /\
           (find_var_decl_by_num id ts' = NONE ==>
            !tv v imms.
              FLOOKUP (get_source_immutables src
                (case ALOOKUP imms cx.txn.target of
                   NONE => [] | SOME m => m)) id = SOME (tv, v) ==>
              evaluate_type (get_tenv cx) ty = SOME tv)) /\
        (* flag_members: match module flag declarations *)
        (!src fid ls.
           FLOOKUP env_body.flag_members (src, fid) = SOME ls ==>
           ?ts'. get_module_code cx src = SOME ts' /\
                 lookup_flag fid ts' = SOME ls /\
                 FLOOKUP (get_tenv cx) (string_to_num fid) =
                   SOME (FlagArgs (LENGTH ls))) /\
        evaluate_type (get_tenv cx) ret = SOME ret_tv /\
        well_typed_stmts env_body ret body /\
        well_typed_exprs
          <| var_types := FEMPTY;
             global_types := FEMPTY;
             toplevel_types := FEMPTY;
             type_defs := get_tenv cx;
             fn_sigs := FEMPTY;
             flag_members := FEMPTY |> dflts /\
        (!id typ. MEM (id, typ) args ==>
           FLOOKUP env_body.var_types (string_to_num id) = SOME typ) /\
        MAP expr_type dflts =
          MAP SND (DROP (LENGTH args - LENGTH dflts) args)
End

(* ===== context_well_typed: transaction fields fit declared types ===== *)
(*
 * The Vyper interpreter's Env builtins (ValueSent, TimeStamp, etc.) return
 * IntV &(cx.txn.field) where field is a num. For the result to satisfy
 * value_has_type (BaseTV (UintT 256)), we need field < 2^256.
 * Since cx is immutable during evaluation, this is trivially preserved
 * by every eval_* function — no preservation lemma needed.
 *
 * See type_preservation_P7_counterexample in vyperTypeSoundnessScript.sml
 * for a formal proof that type_preservation is FALSE without this.
 *)
Definition context_well_typed_def:
  context_well_typed cx <=>
    cx.txn.value < 2 ** 256 /\
    cx.txn.time_stamp < 2 ** 256 /\
    cx.txn.block_number < 2 ** 256 /\
    cx.txn.blob_base_fee < 2 ** 256 /\
    cx.txn.gas_price < 2 ** 256 /\
    cx.txn.chain_id < 2 ** 256 /\
    cx.txn.gas_limit < 2 ** 256 /\
    cx.txn.base_fee < 2 ** 256 /\
    cx.txn.prev_randao < 2 ** 256
End

(* Separate predicate: call site type annotations match function return types *)

Definition loc_type_def:
  loc_type cx st (ScopedVar s) tv =
    (?entry. lookup_scopes (string_to_num s) st.scopes = SOME entry /\
             entry.type = tv) /\
  loc_type cx st (ImmutableVar s) tv =
    (?imms a. get_immutables cx (current_module cx) st = (INL imms, st) /\
              FLOOKUP imms (string_to_num s) = SOME (tv, a)) /\
  loc_type cx st (TopLevelVar src s) tv = F
End

Definition toplevel_value_wf_def[simp]:
  (toplevel_value_wf (Value _) = T) /\
  (toplevel_value_wf (ArrayRef _ _ elem_tv bd) =
     well_formed_type_value (ArrayTV elem_tv bd)) /\
  (toplevel_value_wf (HashMapRef _ _ _ _) = T)
End

(* toplevel_value_typed: connects a toplevel_value to its type_value.
   For Value: value_has_type. For ArrayRef: direct type match.
   For HashMapRef: vacuously true (materialise always fails). *)
Definition toplevel_value_typed_def:
  (toplevel_value_typed (Value v) tyv <=> value_has_type tyv v) /\
  (toplevel_value_typed (ArrayRef _ _ elem_tv bd) tyv <=>
     tyv = ArrayTV elem_tv bd) /\
  (toplevel_value_typed (HashMapRef _ _ _ _) tyv <=> (tyv = NoneTV))
End


