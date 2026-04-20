(*
 * Type soundness definitions for the Vyper interpreter.
 *
 * TOP-LEVEL PREDICATES (external API):
 *   well_typed_expr / well_typed_stmt / well_typed_stmts
 *     — static well-typedness of AST nodes
 *   state_well_typed — runtime state has consistent types
 *   env_consistent — typing env matches runtime context
 *   functions_well_typed — all callable functions have well-typed bodies
 *   context_well_typed — transaction context fields fit their types
 *   accounts_well_typed — account state fields fit their types
 *
 * HELPER DEFINITIONS:
 *   typing_env — record of type environments for expr/stmt typing
 *   fn_sig — function signature (param types, num defaults, return type)
 *   well_typed_literal / well_typed_binop / well_typed_builtin_app
 *     — sub-predicates for literal/op/builtin typing
 *   is_int_type / is_numeric_type / is_comparable_type / etc.
 *     — type classification predicates
 *   subscript_type_ok / attribute_type_ok — subscript/attribute result types
 *   loc_type / toplevel_value_typed — runtime location/value typing
 *)

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

(* Bytes-or-string (no arrays): argument shape accepted by hashes,
   slice, method_id, etc. *)
Definition is_bytes_or_string_type_def[simp]:
  is_bytes_or_string_type (BaseT (StringT _)) = T /\
  is_bytes_or_string_type (BaseT (BytesT _)) = T /\
  is_bytes_or_string_type _ = F
End

(* Scalar types for which Eq/NotEq are defined by evaluate_binop.
   Matches the value constructors supported in the Eq case of
   evaluate_binop_def: IntV, FlagV, StringV, BytesV, BoolV, DecimalV.
   Notably excludes TupleT, ArrayT, StructT, NoneT. *)
Definition is_comparable_type_def[simp]:
  is_comparable_type (BaseT _) = T /\
  is_comparable_type (FlagT _) = T /\
  is_comparable_type _ = F
End


(* ===== well_typed_literal =====
 *
 * A literal fits a base type if its value satisfies the type's value
 * constraint. Type-level well-formedness (e.g. k ≤ 256 for UintT k,
 * n ≤ 32 for fixed bytes) is enforced separately by well_formed_type
 * at the Literal case in well_typed_expr, so it is not repeated here.
 *)
Definition well_typed_literal_def:
  well_typed_literal (BaseT BoolT) (BoolL _) = T /\
  well_typed_literal (BaseT (UintT k)) (IntL n) =
    within_int_bound (Unsigned k) n /\
  well_typed_literal (BaseT (IntT k)) (IntL n) =
    within_int_bound (Signed k) n /\
  well_typed_literal (BaseT DecimalT) (DecimalL n) =
    within_int_bound (Signed 168) n /\
  well_typed_literal (BaseT (StringT n)) (StringL s) =
    (LENGTH s <= n) /\
  well_typed_literal (BaseT (BytesT bd)) (BytesL bs) =
    compatible_bound bd (LENGTH bs) /\
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
  (* Equality: same comparable type (scalar or flag) on both sides *)
  well_typed_binop ty Eq t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_comparable_type t1) /\
  well_typed_binop ty NotEq t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_comparable_type t1) /\
  (* Ordering: numeric only (evaluate_binop accepts IntV/DecimalV) *)
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
  (* Membership: result is bool. evaluate_binop supports two shapes:
       (a) flag-in-flag: both FlagV of the same flag type
       (b) value-in-array: t2 is ArrayT t1 _ *)
  well_typed_binop ty In t1 t2 =
    (ty = BaseT BoolT /\
     ((?fid. t1 = FlagT fid /\ t2 = FlagT fid) \/
      (?bd. t2 = ArrayT t1 bd))) /\
  well_typed_binop ty NotIn t1 t2 =
    (ty = BaseT BoolT /\
     ((?fid. t1 = FlagT fid /\ t2 = FlagT fid) \/
      (?bd. t2 = ArrayT t1 bd)))
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
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32)) /\
     is_bytes_or_string_type (HD ts)) /\
  (* AsWeiValue: numeric -> uint256 *)
  well_typed_builtin_app ty (AsWeiValue _) ts =
    (LENGTH ts = 1 /\ ty = BaseT (UintT 256) /\ is_numeric_type (HD ts)) /\
  (* Concat: 2+ bytes/string args -> bytes/string.
     Argument types must be consistent with result type:
     all BytesT for bytes result, all StringT for string result.
     NOTE: bound n is not related to the sum of argument bounds here;
     runtime bound checking is performed by evaluate_concat. *)
  well_typed_builtin_app ty (Concat n) ts =
    (2 <= LENGTH ts /\
     ((ty = BaseT (BytesT (Dynamic n)) /\
       EVERY (\t. ?bd. t = BaseT (BytesT bd)) ts) \/
      (ty = BaseT (StringT n) /\
       EVERY (\t. ?m. t = BaseT (StringT m)) ts))) /\
  (* Slice: source, start, length -> bytes/string.
     First arg type must be consistent with result type.
     Start and length are uint256 (evaluate_slice uses dest_NumV which
     rejects negatives; Vyper restricts these to uint256). *)
  well_typed_builtin_app ty (Slice n) ts =
    (LENGTH ts = 3 /\
     EL 1 ts = BaseT (UintT 256) /\ EL 2 ts = BaseT (UintT 256) /\
     ((ty = BaseT (BytesT (Dynamic n)) /\
       ?bd. HD ts = BaseT (BytesT bd)) \/
      (ty = BaseT (StringT n) /\
       ?m. HD ts = BaseT (StringT m)))) /\
  (* Uint2Str: uint -> string. The bound n = ceil(log10(2**256)) = 78
     digits suffices for uint256; narrower uints need fewer. Argument
     must be unsigned: evaluate_builtin passes Num i to
     num_to_dec_string, which silently yields 0 for negative inputs. *)
  well_typed_builtin_app ty (Uint2Str n) ts =
    (LENGTH ts = 1 /\ ty = BaseT (StringT n) /\
     (?k. HD ts = BaseT (UintT k)) /\ 78 <= n) /\
  (* MakeArray: constructs a tuple or array from values.
     - type_opt = NONE: tuple construction, result is TupleT with element
       types matching the argument types (heterogeneous allowed)
     - type_opt = SOME elem_ty: array construction, result is ArrayT elem_ty bd,
       and all arguments must have type elem_ty (homogeneous) *)
  well_typed_builtin_app ty (MakeArray NONE bd) ts =
    (ty = TupleT ts /\ compatible_bound bd (LENGTH ts)) /\
  well_typed_builtin_app ty (MakeArray (SOME elem_ty) bd) ts =
    (ty = ArrayT elem_ty bd /\
     compatible_bound bd (LENGTH ts) /\
     EVERY ($= elem_ty) ts) /\
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
  (* Acc: account field access. Takes an address (as bytes) and returns
     the specified field. Type soundness requires an accounts_well_typed
     invariant (balances < 2^256, code length < 2^256, etc.) which is
     added to the global preconditions. *)
  well_typed_builtin_app ty (Acc item) ts =
    (LENGTH ts = 1 /\
     (?bd. HD ts = BaseT (BytesT bd)) /\
     ty = account_item_type item) /\
  (* Isqrt: uint256 -> uint256 *)
  well_typed_builtin_app ty Isqrt ts =
    (ts = [BaseT (UintT 256)] /\
     ty = BaseT (UintT 256)) /\
  (* MethodId: bytes/string -> bytes4 *)
  well_typed_builtin_app ty MethodId ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 4)) /\
     is_bytes_or_string_type (HD ts)) /\
  (* ecrecover(hash, v, r, s) -> address.
     evaluate_ecrecover accepts each of v, r, s as either a uint256 or
     a 32-byte value (see ecrecover_arg_to_num), and the hash must be
     a 32-byte value. *)
  well_typed_builtin_app ty ECRecover ts =
    (LENGTH ts = 4 /\ ty = BaseT AddressT /\
     HD ts = BaseT (BytesT (Fixed 32)) /\
     EVERY (\t. t = BaseT (UintT 256) \/
                t = BaseT (BytesT (Fixed 32))) (TL ts)) /\
  well_typed_builtin_app ty ECAdd ts =
    (LENGTH ts = 2 /\ ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EVERY (\t. t = ArrayT (BaseT (UintT 256)) (Fixed 2)) ts) /\
  (* ECMul: point * scalar -> point. First arg is a point (2-element array
     of uint256), second arg is an integer scalar. *)
  well_typed_builtin_app ty ECMul ts =
    (LENGTH ts = 2 /\ ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EL 0 ts = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     is_int_type (EL 1 ts)) /\
  (* PowMod256: 2x uint256 -> uint256 *)
  well_typed_builtin_app ty PowMod256 ts =
    (ts = [BaseT (UintT 256); BaseT (UintT 256)] /\
     ty = BaseT (UintT 256)) /\
  (* Abs: numeric -> same type *)
  well_typed_builtin_app ty Abs ts =
    (ts = [ty] /\ is_numeric_type ty) /\
  (* Sha256: bytes/string -> bytes32 *)
  well_typed_builtin_app ty Sha256 ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32)) /\
     is_bytes_or_string_type (HD ts))
End

(* ===== Type well-formedness ===== *)

Definition well_formed_type_def:
  well_formed_type tenv ty = IS_SOME (evaluate_type tenv ty)
End

(* ===== Subscript typing ===== *)
(* Subscripting is defined for:
   - ArrayT: integer index yields element type
   - TupleT: LIMITATION — currently requires homogeneous tuples (all elements
             same type). This is overly restrictive.

     In real Vyper, tuples can be heterogeneous (e.g., (uint256, bool, address))
     but subscripting is only allowed with CONSTANT indices. The Vyper compiler
     statically resolves t[0], t[1], etc. to the correct element type at compile
     time. Variable indices like t[i] are rejected by the compiler.

     The Vyper compiler already provides the correct result type in the AST's
     Subscript node (the first 'type' field). A proper fix would be:

     TODO: Add a new AST node for tuple element access with explicit constant index:
       | TupleElement type expr num   (* result_type, tuple_expr, constant_index *)

     The frontend (jsonToVyperScript.sml) would generate TupleElement instead of
     Subscript when the base is a tuple type and index is a literal. The type rule
     would then check: n < LENGTH ts /\ EL n ts = result_ty.

     For now, programs subscripting heterogeneous tuples fall outside the
     well-typed fragment. Tuple unpacking (via TupleTarget in assignments)
     still works for heterogeneous tuples.

   Other types (BaseT, StructT, FlagT, NoneT) are not subscriptable;
   struct field access uses Attribute, not Subscript. *)
Definition subscript_type_ok_def:
  subscript_type_ok (ArrayT elem_ty _) idx_ty result_ty =
    (result_ty = elem_ty /\ is_int_type idx_ty) /\
  (* TODO: Support heterogeneous tuples via TupleElement AST node (see above) *)
  subscript_type_ok (TupleT ts) idx_ty result_ty =
    (is_int_type idx_ty /\ ts <> [] /\ EVERY ($= result_ty) ts) /\
  (* Explicitly list unsupported types for clarity (no catch-all) *)
  subscript_type_ok (BaseT _) _ _ = F /\
  subscript_type_ok (StructT _) _ _ = F /\
  subscript_type_ok (FlagT _) _ _ = F /\
  subscript_type_ok NoneT _ _ = F
End

(* ===== Attribute typing ===== *)
(* Attribute access is defined only for struct types: looks up the field
   in the struct's declared fields and returns its type.
   Other types (BaseT, TupleT, ArrayT, FlagT, NoneT) do not support
   attribute access via this predicate. *)
Definition attribute_type_ok_def:
  attribute_type_ok tenv (StructT sname) field_id result_ty =
    (case FLOOKUP tenv (string_to_num sname) of
       SOME (StructArgs fields) =>
         (case ALOOKUP fields field_id of
            SOME field_ty => result_ty = field_ty
          | NONE => F)
     | _ => F) /\
  attribute_type_ok _ (BaseT _) _ _ = F /\
  attribute_type_ok _ (TupleT _) _ _ = F /\
  attribute_type_ok _ (ArrayT _ _) _ _ = F /\
  attribute_type_ok _ (FlagT _) _ _ = F /\
  attribute_type_ok _ NoneT _ _ = F
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

(* fn_sig: function signature for IntCall typing.
   param_types: types of all parameters (from MAP SND args)
   num_defaults: number of parameters with default values
   ret_ty: declared return type *)
Datatype:
  fn_sig = <| param_types : type list;
              num_defaults : num;
              ret_ty : type |>
End

Datatype:
  typing_env = <|
    var_types : (num |-> type);
    global_types : (num |-> type);
    toplevel_types : ((num option # num) |-> type);
    type_defs : (num |-> type_args);
    fn_sigs : ((num option # string) |-> fn_sig);
    flag_members : ((num option # string) |-> string list);
  |>
End

(* fn_sigs_consistent: for any function signature in fn_sigs,
   the runtime lookup agrees on param types, default count, and return type *)
Definition fn_sigs_consistent_def:
  fn_sigs_consistent fn_sigs cx <=>
    !src_id_opt fn sig.
      FLOOKUP fn_sigs (src_id_opt, fn) = SOME sig ==>
      ?ts fm nr params dflts body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts =
          SOME (fm, nr, params, dflts, sig.ret_ty, body) /\
        sig.param_types = MAP SND params /\
        sig.num_defaults = LENGTH dflts
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

(* ===== Valid type conversions =====
   Enumerates all valid (source_type, target_type) pairs for convert().
   Based on evaluate_convert_def in vyperValueOperationScript.sml.

   Conversions fall into these categories:
   - To bool: bytes/int → bool (non-zero check)
   - From bool: bool → int/uint
   - Bytes resizing: bytes → bytes (fixed or dynamic)
   - Bytes to numeric: bytes → int/uint
   - Numeric resizing: int/uint → int/uint (with bounds check at runtime)
   - Int to address: int → address (160-bit)
   - Flag conversions: flag ↔ int/uint
   - Int to bytes: int → bytes (fixed or dynamic)
   - String/bytes: bytes ↔ string
   - Decimal: int ↔ decimal
*)
Definition valid_conversion_def:
  (* To bool *)
  valid_conversion (BaseT (BytesT _)) (BaseT BoolT) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT BoolT) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT BoolT) = T /\
  (* From bool *)
  valid_conversion (BaseT BoolT) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT BoolT) (BaseT (UintT _)) = T /\
  (* Bytes resizing *)
  valid_conversion (BaseT (BytesT _)) (BaseT (BytesT _)) = T /\
  (* Bytes to numeric *)
  valid_conversion (BaseT (BytesT _)) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (BytesT _)) (BaseT (IntT _)) = T /\
  (* Numeric resizing *)
  valid_conversion (BaseT (UintT _)) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT (IntT _)) = T /\
  (* Int to address *)
  valid_conversion (BaseT (UintT _)) (BaseT AddressT) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT AddressT) = T /\
  (* Flag to int/uint *)
  valid_conversion (FlagT _) (BaseT (IntT _)) = T /\
  valid_conversion (FlagT _) (BaseT (UintT _)) = T /\
  (* Int/uint to flag *)
  valid_conversion (BaseT (UintT _)) (FlagT _) = T /\
  valid_conversion (BaseT (IntT _)) (FlagT _) = T /\
  (* Int to bytes *)
  valid_conversion (BaseT (UintT _)) (BaseT (BytesT _)) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT (BytesT _)) = T /\
  (* Bytes to string *)
  valid_conversion (BaseT (BytesT _)) (BaseT (StringT _)) = T /\
  (* String resizing *)
  valid_conversion (BaseT (StringT _)) (BaseT (StringT _)) = T /\
  (* String to bytes *)
  valid_conversion (BaseT (StringT _)) (BaseT (BytesT _)) = T /\
  (* Int to decimal *)
  valid_conversion (BaseT (UintT _)) (BaseT DecimalT) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT DecimalT) = T /\
  (* Decimal to int/uint *)
  valid_conversion (BaseT DecimalT) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT DecimalT) (BaseT (UintT _)) = T /\
  (* All other conversions are invalid *)
  valid_conversion _ _ = F
End

(* TypeBuiltin argument typing: each type builtin has specific argument
   requirements. This predicate checks argument count and types.
   - Empty: no arguments (creates default value of the type)
   - MaxValue/MinValue: no arguments (returns max/min for numeric types)
   - Epsilon: no arguments (returns smallest decimal increment)
   - Convert: one argument, must be a valid conversion pair
   - Extract32: two arguments (bytes source, uint256 index)
   - AbiDecode: one argument (bytes to decode)
   - AbiEncode: one or more arguments, target_ty = TupleT of arg types *)
Definition well_typed_type_builtin_args_def:
  well_typed_type_builtin_args Empty target_ty ts = (ts = []) /\
  well_typed_type_builtin_args MaxValue target_ty ts =
    (ts = [] /\ is_numeric_type target_ty) /\
  well_typed_type_builtin_args MinValue target_ty ts =
    (ts = [] /\ is_numeric_type target_ty) /\
  well_typed_type_builtin_args Epsilon target_ty ts =
    (ts = [] /\ target_ty = BaseT DecimalT) /\
  well_typed_type_builtin_args Convert target_ty ts =
    (LENGTH ts = 1 /\ valid_conversion (HD ts) target_ty) /\
  well_typed_type_builtin_args Extract32 target_ty ts =
    (LENGTH ts = 2 /\
     (?bd. EL 0 ts = BaseT (BytesT bd)) /\
     is_int_type (EL 1 ts) /\
     (?bt. target_ty = BaseT bt)) /\
  well_typed_type_builtin_args (AbiDecode _) target_ty ts =
    (LENGTH ts = 1 /\ ?bd. HD ts = BaseT (BytesT bd)) /\
  (* AbiEncode: encodes values as ABI bytes. The target_ty specifies the
     tuple type of the arguments being encoded. Result is bytes. *)
  well_typed_type_builtin_args (AbiEncode _) target_ty ts =
    (ts <> [] /\ target_ty = TupleT ts)
End

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
     expr_type e1 = ty /\ expr_type e2 = ty /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Literal ty l) =
    (well_typed_literal ty l /\
     well_formed_type env.type_defs ty) /\
  (* StructLit: the annotated type must be StructT id, its declaration
     in type_defs must have fields matching the named expression list
     (in order), and each value expression has the declared field type. *)
  well_typed_expr env (StructLit ty nsid kes) =
    (well_typed_named_exprs env kes /\
     well_formed_type env.type_defs ty /\
     ?id args. ty = StructT id /\ SND nsid = id /\
            FLOOKUP env.type_defs (string_to_num id) = SOME (StructArgs args) /\
            MAP FST kes = MAP FST args /\
            MAP (expr_type o SND) kes = MAP SND args) /\
  well_typed_expr env (Subscript ty e1 e2) =
    (well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     subscript_type_ok (expr_type e1) (expr_type e2) ty /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Attribute ty e id) =
    (well_typed_expr env e /\
     attribute_type_ok env.type_defs (expr_type e) id ty /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Builtin ty blt es) =
    (well_typed_exprs env es /\
     well_typed_builtin_app ty blt (MAP expr_type es) /\
     well_formed_type env.type_defs ty) /\
  (* TypeBuiltin: a builtin that takes a type argument.
     For Empty/MaxValue/MinValue/Convert/Epsilon/Extract32/AbiDecode:
       result type = target_ty (the type argument)
     For AbiEncode:
       result type = bytes (dynamic), target_ty = TupleT of argument types *)
  well_typed_expr env (TypeBuiltin ty (AbiEncode ensure) target_ty es) =
    (well_typed_exprs env es /\
     (?n. ty = BaseT (BytesT (Dynamic n))) /\
     target_ty = TupleT (MAP expr_type es) /\
     well_formed_type env.type_defs ty /\
     well_typed_type_builtin_args (AbiEncode ensure) target_ty (MAP expr_type es)) /\
  well_typed_expr env (TypeBuiltin ty tb target_ty es) =
    (well_typed_exprs env es /\
     ty = target_ty /\
     (!b. tb <> AbiEncode b) /\
     well_formed_type env.type_defs ty /\
     well_formed_type env.type_defs target_ty /\
     well_typed_type_builtin_args tb target_ty (MAP expr_type es)) /\
  well_typed_expr env (Pop ty tgt) =
    (?bd. well_typed_target env tgt (ArrayT ty bd)) /\
  (* IntCall: internal function call. Argument count must be in the range
     [LENGTH param_types - num_defaults, LENGTH param_types], and the
     provided argument types must match the first LENGTH args param types.
     The return type annotation must match the function's declared return. *)
  well_typed_expr env (Call ty (IntCall (src_id_opt, fn_name)) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     well_formed_type env.type_defs ty /\
     ?sig.
       FLOOKUP env.fn_sigs (src_id_opt, fn_name) = SOME sig /\
       ty = sig.ret_ty /\
       LENGTH args <= LENGTH sig.param_types /\
       LENGTH sig.param_types - sig.num_defaults <= LENGTH args /\
       MAP expr_type args = TAKE (LENGTH args) sig.param_types) /\
  well_typed_expr env (Call ty (ExtCall _ (_, arg_types, ret_ty)) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     well_formed_type env.type_defs ty /\
     ty = ret_ty /\
     MAP expr_type args = arg_types /\
     (!e. drv = SOME e ==> expr_type e = ret_ty)) /\
  (* send(to, value): transfers ether. drv is unused (send always succeeds
     or reverts); value must be uint256 (dest_NumV rejects negatives). *)
  well_typed_expr env (Call ty Send args drv) =
    (well_typed_exprs env args /\
     drv = NONE /\
     LENGTH args = 2 /\ ty = NoneT /\
     HD (MAP expr_type args) = BaseT AddressT /\
     EL 1 (MAP expr_type args) = BaseT (UintT 256)) /\
  (* raw_call(to, data, value): value is uint256. *)
  well_typed_expr env (Call ty (RawCallTarget flags) args drv) =
    (well_typed_exprs env args /\
     drv = NONE /\
     ty = raw_call_return_type flags /\
     flags.rcf_max_outsize < dimword(:256) /\
     LENGTH args = 3 /\
     EL 0 (MAP expr_type args) = BaseT AddressT /\
     (?bd. EL 1 (MAP expr_type args) = BaseT (BytesT bd)) /\
     EL 2 (MAP expr_type args) = BaseT (UintT 256)) /\
  (* raw_log(topics, data): topics is array of bytes32, data is bytes. *)
  well_typed_expr env (Call ty RawLog args drv) =
    (well_typed_exprs env args /\
     drv = NONE /\
     ty = NoneT /\
     LENGTH args = 2 /\
     (?bd. EL 0 (MAP expr_type args) = ArrayT (BaseT (BytesT (Fixed 32))) bd) /\
     (?bd'. EL 1 (MAP expr_type args) = BaseT (BytesT bd'))) /\
  (* raw_revert(data): terminates execution, never returns.
     The type annotation is NoneT for consistency. *)
  well_typed_expr env (Call ty RawRevert args drv) =
    (well_typed_exprs env args /\
     drv = NONE /\
     ty = NoneT /\
     LENGTH args = 1 /\
     (?bd. HD (MAP expr_type args) = BaseT (BytesT bd))) /\
  (* selfdestruct(to): terminates execution, no drv. *)
  well_typed_expr env (Call ty SelfDestructTarget args drv) =
    (well_typed_exprs env args /\
     drv = NONE /\
     ty = NoneT /\
     LENGTH args = 1 /\
     HD (MAP expr_type args) = BaseT AddressT) /\
  (* create_*(target, ...ctor_args, value): value is uint256. *)
  well_typed_expr env (Call ty (CreateTarget kind rof) args drv) =
    (well_typed_exprs env args /\
     drv = NONE /\
     ty = BaseT AddressT /\
     LENGTH args >= 2 /\
     HD (MAP expr_type args) = BaseT AddressT /\
     LAST (MAP expr_type args) = BaseT (UintT 256)) /\
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
  (* RaiseReason: the reason expression must be a string *)
  well_typed_stmt env ret_ty (Raise (RaiseReason e)) =
    (well_typed_expr env e /\
     ?n. expr_type e = BaseT (StringT n)) /\
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
(* functions_well_typed cx:
 *   There exists a single global fn_sigs map (and supporting toplevel_types,
 *   flag_members) that is consistent with cx, and under which every callable
 *   function's body is well-typed.
 *
 *   For every callable function:
 *   1. If nonreentrant, cx has a nonreentrant slot
 *   2. There exists a typing env env_body with matching type_defs
 *   3. The return type evaluates successfully
 *   4. The function body is well-typed under env_body
 *   5. Default values are well-typed (in a minimal env with no local var refs)
 *   6. Each parameter is tracked in env_body.var_types
 *   7. env_body.toplevel_types match storage declarations
 *   8. env_body.flag_members match module flag declarations
 *)
Definition functions_well_typed_def:
  functions_well_typed cx <=>
    ?fn_sigs toplevel_types flag_members.
      fn_sigs_consistent fn_sigs cx /\
      !src_id_opt fn ts fm nr args dflts ret body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts =
          SOME (fm, nr, args, dflts, ret, body) ==>
        (nr ==> cx.nonreentrant_slot <> NONE) /\
        ?env_body ret_tv.
          env_body.type_defs = get_tenv cx /\
          env_body.fn_sigs = fn_sigs /\
          env_body.global_types = FEMPTY /\
          env_body.toplevel_types = toplevel_types /\
          env_body.flag_members = flag_members /\
          (* toplevel_types: match storage decls + immutable type consistency *)
          (!src id ty ts'.
             FLOOKUP toplevel_types (src, id) = SOME ty /\
             get_module_code cx src = SOME ts' ==>
             (!is_transient typ id_str.
                find_var_decl_by_num id ts' =
                  SOME (StorageVarDecl is_transient typ, id_str) ==>
                typ = ty) /\
             (!is_transient kt vt id_str.
                find_var_decl_by_num id ts' =
                  SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
                ty = NoneT) /\
             (* Immutable case: note we don't have st here, so we
                require that evaluate_type is defined for the declared
                type. The runtime consistency check is in env_consistent. *)
             (find_var_decl_by_num id ts' = NONE ==>
              IS_SOME (evaluate_type (get_tenv cx) ty))) /\
          (* flag_members: match module flag declarations *)
          (!src fid ls.
             FLOOKUP flag_members (src, fid) = SOME ls ==>
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

(* ===== accounts_well_typed: account fields fit declared types ===== *)
(*
 * The Acc builtins (Balance, Codesize, etc.) return values from account
 * state. For these to satisfy value_has_type, we need:
 *   - balance < 2^256 (for uint256)
 *   - code length < 2^256 (for uint256 codesize)
 *   - code length <= 24576 (for bytes[24576] code, per EIP-170)
 * The accounts map is part of the external state passed to the interpreter.
 *)
Definition account_well_typed_def:
  account_well_typed (a : account_state) <=>
    a.balance < 2 ** 256 /\
    LENGTH a.code <= 24576
End

Definition accounts_well_typed_def:
  accounts_well_typed acc <=>
    !addr. account_well_typed (lookup_account addr acc)
End

(* Separate predicate: call site type annotations match function return types *)

(* loc_type: runtime type of a target location.
   Used to connect well_typed_target to the runtime state.
   TopLevelVar is explicitly F because top-level storage variables don't
   have a fixed type_value in the scope — their types come from
   toplevel_types in the typing env (see eval_base_target_type_connection
   in vyperTypeSoundnessHelpersScript). *)
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


