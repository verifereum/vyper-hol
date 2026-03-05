(*
 * vyperTypeCheckScript.sml
 *
 * Type checking for the Vyper AST with checked type annotations.
 *
 * TOP-LEVEL:
 *   satisfies_type    : value → type_value → bool  (value matches resolved type)
 *   well_typed_literal : type → literal → bool     (literal consistent with type)
 *   well_typed_expr   : typing_env → expr → bool   (AST annotations consistent)
 *   type_soundness    : well_typed + eval succeeds ⇒ satisfies_type (CHEATED)
 *
 * Helper:
 *   is_numeric_type, is_int_type, is_bool_type, is_flag_type : type → bool
 *   well_typed_binop  : type → binop → type → type → bool
 *   well_typed_builtin_app : type → builtin → type list → bool
 *   env_item_type, account_item_type : item → type
 *   well_formed_type  : (num |-> type_args) → type → bool
 *   all_satisfy_type, list_satisfies_type : list helpers for satisfies_type
 *)

Theory vyperTypeCheck
Ancestors
  vyperAST vyperValue vyperMisc
  vyperInterpreter vyperState

(* ===== Type Classification Helpers ===== *)

Definition is_numeric_type_def:
  is_numeric_type (BaseT (UintT _)) = T /\
  is_numeric_type (BaseT (IntT _)) = T /\
  is_numeric_type (BaseT DecimalT) = T /\
  is_numeric_type _ = F
End

Definition is_int_type_def:
  is_int_type (BaseT (UintT _)) = T /\
  is_int_type (BaseT (IntT _)) = T /\
  is_int_type _ = F
End

Definition is_bool_type_def:
  is_bool_type (BaseT BoolT) = T /\
  is_bool_type _ = F
End

Definition is_flag_type_def:
  is_flag_type (FlagT _) = T /\
  is_flag_type _ = F
End

Definition is_sized_type_def:
  is_sized_type (ArrayT _ _) = T /\
  is_sized_type (BaseT (StringT _)) = T /\
  is_sized_type (BaseT (BytesT _)) = T /\
  is_sized_type _ = F
End

(* ===== satisfies_type: value matches resolved type ===== *)

Definition satisfies_type_def:
  (* base types *)
  satisfies_type NoneV NoneTV = T /\
  satisfies_type (BoolV _) (BaseTV BoolT) = T /\
  satisfies_type (IntV n) (BaseTV (UintT k)) =
    (0 <= n /\ Num n < 2 ** k) /\
  satisfies_type (IntV n) (BaseTV (IntT k)) =
    within_int_bound (Signed k) n /\
  satisfies_type (DecimalV n) (BaseTV DecimalT) =
    within_int_bound (Signed 168) n /\
  satisfies_type (StringV s) (BaseTV (StringT n)) =
    (LENGTH s <= n) /\
  satisfies_type (BytesV bs) (BaseTV (BytesT bd)) =
    compatible_bound bd (LENGTH bs) /\
  satisfies_type (BytesV bs) (BaseTV AddressT) =
    (LENGTH bs = 20) /\
  satisfies_type (FlagV m) (FlagTV n) =
    (m < 2 ** n) /\
  (* compound types *)
  satisfies_type (ArrayV (DynArrayV n vs)) (ArrayTV tv (Dynamic m)) =
    (n = m /\ LENGTH vs <= m /\ all_satisfy_type vs tv) /\
  satisfies_type (ArrayV (SArrayV n al)) (ArrayTV tv (Fixed m)) =
    (n = m /\ ALL_DISTINCT (MAP FST al) /\
     EVERY (\(k,_). k < n) al /\
     all_satisfy_type (MAP SND al) tv) /\
  satisfies_type (ArrayV (TupleV vs)) (TupleTV ts) =
    list_satisfies_type vs ts /\
  satisfies_type (StructV al) (StructTV args) =
    (MAP FST al = MAP FST args /\
     list_satisfies_type (MAP SND al) (MAP SND args)) /\
  satisfies_type _ _ = F /\
  (* list helpers *)
  all_satisfy_type [] _ = T /\
  all_satisfy_type (v::vs) tv =
    (satisfies_type v tv /\ all_satisfy_type vs tv) /\
  list_satisfies_type [] [] = T /\
  list_satisfies_type (v::vs) (tv::ts) =
    (satisfies_type v tv /\ list_satisfies_type vs ts) /\
  list_satisfies_type _ _ = F
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (v, _) => value_size v
    | INR (INL (vs, _)) => list_size value_size vs
    | INR (INR (vs, _)) => list_size value_size vs)`
  \\ rw[list_size_pair_size_map]
End

(* ===== well_typed_literal ===== *)

Definition well_typed_literal_def:
  well_typed_literal (BaseT BoolT) (BoolL _) = T /\
  well_typed_literal (BaseT (UintT k)) (IntL (Unsigned k') n) =
    (k = k' /\ within_int_bound (Unsigned k) n) /\
  well_typed_literal (BaseT (IntT k)) (IntL (Signed k') n) =
    (k = k' /\ within_int_bound (Signed k) n) /\
  well_typed_literal (BaseT DecimalT) (DecimalL n) =
    within_int_bound (Signed 168) n /\
  well_typed_literal (BaseT (StringT n)) (StringL m s) =
    (n = m /\ LENGTH s <= n) /\
  well_typed_literal (BaseT (BytesT bd)) (BytesL bd' bs) =
    (bd = bd' /\ compatible_bound bd (LENGTH bs)) /\
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
  (* Membership: result is bool *)
  well_typed_binop ty In t1 t2 =
    (ty = BaseT BoolT /\ is_ArrayT t2) /\
  well_typed_binop ty NotIn t1 t2 =
    (ty = BaseT BoolT /\ is_ArrayT t2)
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
  env_item_type ChainId = BaseT (UintT 256)
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
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32))) /\
  (* AsWeiValue: numeric -> uint256 *)
  well_typed_builtin_app ty (AsWeiValue _) ts =
    (LENGTH ts = 1 /\ ty = BaseT (UintT 256)) /\
  (* Concat: 2+ bytes/string args -> bytes/string *)
  well_typed_builtin_app ty (Concat n) ts =
    (2 <= LENGTH ts /\
     (ty = BaseT (BytesT (Dynamic n)) \/
      ty = BaseT (StringT n))) /\
  (* Slice: source, start, length -> bytes/string *)
  well_typed_builtin_app ty (Slice n) ts =
    (LENGTH ts = 3 /\
     (ty = BaseT (BytesT (Dynamic n)) \/
      ty = BaseT (StringT n))) /\
  (* Uint2Str: uint -> string *)
  well_typed_builtin_app ty (Uint2Str n) ts =
    (LENGTH ts = 1 /\ ty = BaseT (StringT n) /\
     is_int_type (HD ts)) /\
  (* MakeArray: elements -> array or tuple *)
  well_typed_builtin_app ty (MakeArray type_opt bd) ts =
    (compatible_bound bd (LENGTH ts) /\
     (case type_opt of
        NONE => is_TupleT ty
      | SOME t => ty = ArrayT t bd)) /\
  (* Ceil/Floor: decimal -> int *)
  well_typed_builtin_app ty Ceil ts =
    (LENGTH ts = 1 /\ HD ts = BaseT DecimalT /\
     is_int_type ty) /\
  well_typed_builtin_app ty Floor ts =
    (LENGTH ts = 1 /\ HD ts = BaseT DecimalT /\
     is_int_type ty) /\
  (* AddMod/MulMod: 3x uint256 -> uint256 *)
  well_typed_builtin_app ty AddMod ts =
    (LENGTH ts = 3 /\ ty = BaseT (UintT 256) /\
     EVERY (\t. t = BaseT (UintT 256)) ts) /\
  well_typed_builtin_app ty MulMod ts =
    (LENGTH ts = 3 /\ ty = BaseT (UintT 256) /\
     EVERY (\t. t = BaseT (UintT 256)) ts) /\
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
  (* Acc: address -> type depends on item *)
  well_typed_builtin_app ty (Acc item) ts =
    (LENGTH ts = 1 /\ HD ts = BaseT AddressT /\
     ty = account_item_type item) /\
  (* Isqrt: uint256 -> uint256 *)
  well_typed_builtin_app ty Isqrt ts =
    (ts = [BaseT (UintT 256)] /\
     ty = BaseT (UintT 256)) /\
  (* MethodId: string/bytes -> bytes4 *)
  well_typed_builtin_app ty MethodId ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 4))) /\
  (* EC operations *)
  well_typed_builtin_app ty ECRecover ts =
    (LENGTH ts = 4 /\ ty = BaseT AddressT) /\
  well_typed_builtin_app ty ECAdd ts =
    (LENGTH ts = 2 /\ is_TupleT ty) /\
  well_typed_builtin_app ty ECMul ts =
    (LENGTH ts = 2 /\ is_TupleT ty) /\
  (* PowMod256: 2x uint256 -> uint256 *)
  well_typed_builtin_app ty PowMod256 ts =
    (ts = [BaseT (UintT 256); BaseT (UintT 256)] /\
     ty = BaseT (UintT 256))
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
    (is_int_type idx_ty /\ MEM result_ty ts) /\
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

(* ===== Typing environment ===== *)

Datatype:
  typing_env = <|
    var_types : (num |-> type);      (* local variable types *)
    global_types : (num |-> type);   (* constants/immutables *)
    toplevel_types : ((num option # num) |-> type);
                                     (* module-qualified globals: (src_id, name) -> type *)
    type_defs : (num |-> type_args); (* struct/flag declarations *)
  |>
End

(* ===== well_typed_expr: AST annotation consistency ===== *)
(*
 * Mutually recursive with:
 *   well_typed_target : typing_env -> base_assignment_target -> bool
 *   well_typed_exprs  : typing_env -> expr list -> bool
 *   well_typed_opt    : typing_env -> expr option -> bool
 *   well_typed_named_exprs : typing_env -> (identifier # expr) list -> bool
 *)

Definition well_typed_expr_def:
  (* --- expr cases --- *)

  (* Name: variable in scope with matching type *)
  well_typed_expr env (Name ty id) =
    (FLOOKUP env.var_types (string_to_num id) = SOME ty) /\

  (* BareGlobalName: constant/immutable with matching type *)
  well_typed_expr env (BareGlobalName ty id) =
    (FLOOKUP env.global_types (string_to_num id) = SOME ty) /\

  (* TopLevelName: module-qualified global with matching type *)
  well_typed_expr env (TopLevelName ty (src_id_opt, id)) =
    (FLOOKUP env.toplevel_types (src_id_opt, string_to_num id) = SOME ty) /\

  (* FlagMember: must be a flag type *)
  well_typed_expr env (FlagMember ty _ _) =
    is_flag_type ty /\

  (* IfExp: condition is bool, branches have result type *)
  well_typed_expr env (IfExp ty cond e1 e2) =
    (well_typed_expr env cond /\
     well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     expr_type cond = BaseT BoolT /\
     expr_type e1 = ty /\ expr_type e2 = ty) /\

  (* Literal: literal consistent with annotated type *)
  well_typed_expr env (Literal ty l) =
    well_typed_literal ty l /\

  (* StructLit: fields well-typed, result is struct type *)
  well_typed_expr env (StructLit ty _ kes) =
    (well_typed_named_exprs env kes /\
     (case ty of StructT _ => T | _ => F)) /\

  (* Subscript: array/tuple subscript *)
  well_typed_expr env (Subscript ty e1 e2) =
    (well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     subscript_type_ok (expr_type e1) (expr_type e2) ty) /\

  (* Attribute: struct field access *)
  well_typed_expr env (Attribute ty e id) =
    (well_typed_expr env e /\
     attribute_type_ok env.type_defs (expr_type e) id ty) /\

  (* Builtin: sub-exprs well-typed, builtin typing rules *)
  well_typed_expr env (Builtin ty blt es) =
    (well_typed_exprs env es /\
     well_typed_builtin_app ty blt (MAP expr_type es)) /\

  (* TypeBuiltin: sub-exprs well-typed, both types well-formed *)
  well_typed_expr env (TypeBuiltin ty _ target_ty es) =
    (well_typed_exprs env es /\
     well_formed_type env.type_defs ty /\
     well_formed_type env.type_defs target_ty) /\

  (* Pop: target well-typed, result is element type of array *)
  well_typed_expr env (Pop ty tgt) =
    (well_typed_target env tgt /\
     well_formed_type env.type_defs ty) /\

  (* Call IntCall: args well-typed, return type well-formed *)
  well_typed_expr env (Call ty (IntCall _) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     well_formed_type env.type_defs ty) /\

  (* Call ExtCall: args well-typed, return type matches signature *)
  well_typed_expr env (Call ty (ExtCall _ (_, arg_types, ret_ty)) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     ty = ret_ty) /\

  (* Call Send: exactly 2 args (address, value), returns None *)
  well_typed_expr env (Call ty Send args drv) =
    (well_typed_exprs env args /\
     LENGTH args = 2 /\ ty = NoneT) /\

  (* --- base_assignment_target cases --- *)

  well_typed_target env (NameTarget id) =
    (string_to_num id IN FDOM env.var_types) /\

  well_typed_target env (BareGlobalNameTarget id) =
    (string_to_num id IN FDOM env.global_types) /\

  well_typed_target env (TopLevelNameTarget (src_id_opt, id)) =
    ((src_id_opt, string_to_num id) IN FDOM env.toplevel_types) /\

  well_typed_target env (SubscriptTarget tgt e) =
    (well_typed_target env tgt /\ well_typed_expr env e) /\

  well_typed_target env (AttributeTarget tgt _) =
    well_typed_target env tgt /\

  (* --- list/option helpers --- *)

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
    | INR (INL (_, tgt)) => base_assignment_target_size tgt
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

(* ===== Soundness theorem (CHEATED) ===== *)

Theorem type_soundness:
  !env cx e st v st' tv.
    well_typed_expr env e /\
    eval_expr cx e st = (INL (Value v), st') /\
    evaluate_type env.type_defs (expr_type e) = SOME tv
    ==> satisfies_type v tv
Proof
  cheat
QED
