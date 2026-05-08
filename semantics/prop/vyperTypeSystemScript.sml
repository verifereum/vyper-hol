(*
 * Fresh executable type system for Vyper.
 *
 * This is intended to replace vyperTypeSoundnessDefs eventually.
 * It contains definitions only/minimal proof obligations: executable typing
 * predicates/functions, runtime invariants, and global consistency predicates.
 *)

Theory vyperTypeSystem
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage
  vyperTyping vyperEncodeDecode vyperArith
Libs
  wordsLib

(* ===== Basic type classifiers ===== *)

Definition is_int_type_def[simp]:
  is_int_type (BaseT (UintT _)) = T /\
  is_int_type (BaseT (IntT _)) = T /\
  is_int_type _ = F
End

Definition is_uint256_type_def[simp]:
  is_uint256_type (BaseT (UintT 256)) = T /\
  is_uint256_type _ = F
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

Definition is_sized_type_def[simp]:
  is_sized_type (ArrayT _ _) = T /\
  is_sized_type (BaseT (StringT _)) = T /\
  is_sized_type (BaseT (BytesT _)) = T /\
  is_sized_type _ = F
End

Definition is_bytes_or_string_type_def[simp]:
  is_bytes_or_string_type (BaseT (StringT _)) = T /\
  is_bytes_or_string_type (BaseT (BytesT _)) = T /\
  is_bytes_or_string_type _ = F
End

Definition is_comparable_type_def[simp]:
  is_comparable_type (BaseT _) = T /\
  is_comparable_type (FlagT _) = T /\
  is_comparable_type _ = F
End

(* ===== Literals, binops, builtins ===== *)

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

Definition well_typed_binop_def:
  well_typed_binop ty Add t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Sub t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Mul t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Div t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Mod t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Exp t1 t2 = (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty ExpMod t1 t2 = (t1 = ty /\ t2 = ty /\ ty = BaseT (UintT 256)) /\
  well_typed_binop ty UAdd t1 t2 = (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty USub t1 t2 = (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty UMul t1 t2 = (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty UDiv t1 t2 = (t1 = ty /\ t2 = ty /\ is_int_type ty) /\
  well_typed_binop ty ShL t1 t2 = (t1 = ty /\ is_int_type ty /\ is_int_type t2) /\
  well_typed_binop ty ShR t1 t2 = (t1 = ty /\ is_int_type ty /\ is_int_type t2) /\
  well_typed_binop ty And t1 t2 =
    (t1 = ty /\ t2 = ty /\ (is_int_type ty \/ is_bool_type ty \/ is_flag_type ty)) /\
  well_typed_binop ty Or t1 t2 =
    (t1 = ty /\ t2 = ty /\ (is_int_type ty \/ is_bool_type ty \/ is_flag_type ty)) /\
  well_typed_binop ty XOr t1 t2 =
    (t1 = ty /\ t2 = ty /\ (is_int_type ty \/ is_bool_type ty \/ is_flag_type ty)) /\
  well_typed_binop ty Eq t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_comparable_type t1) /\
  well_typed_binop ty NotEq t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_comparable_type t1) /\
  well_typed_binop ty Lt t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty LtE t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty Gt t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty GtE t1 t2 =
    (t1 = t2 /\ ty = BaseT BoolT /\ is_numeric_type t1) /\
  well_typed_binop ty Min t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty Max t1 t2 = (t1 = ty /\ t2 = ty /\ is_numeric_type ty) /\
  well_typed_binop ty In t1 t2 =
    (ty = BaseT BoolT /\ ((?fid. t1 = FlagT fid /\ t2 = FlagT fid) \/
                          (?bd. t2 = ArrayT t1 bd))) /\
  well_typed_binop ty NotIn t1 t2 =
    (ty = BaseT BoolT /\ ((?fid. t1 = FlagT fid /\ t2 = FlagT fid) \/
                          (?bd. t2 = ArrayT t1 bd)))
End

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

Definition well_typed_builtin_app_def:
  well_typed_builtin_app ty (Bop bop) ts =
    (LENGTH ts = 2 /\ well_typed_binop ty bop (EL 0 ts) (EL 1 ts)) /\
  well_typed_builtin_app ty Len ts =
    (LENGTH ts = 1 /\ ty = BaseT (UintT 256) /\ is_sized_type (HD ts)) /\
  well_typed_builtin_app ty Not ts =
    (LENGTH ts = 1 /\ HD ts = ty /\ (is_bool_type ty \/ is_int_type ty \/ is_flag_type ty)) /\
  well_typed_builtin_app ty Neg ts = (ts = [ty] /\ is_numeric_type ty) /\
  well_typed_builtin_app ty Keccak256 ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32)) /\ is_bytes_or_string_type (HD ts)) /\
  well_typed_builtin_app ty Sha256 ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 32)) /\ is_bytes_or_string_type (HD ts)) /\
  well_typed_builtin_app ty (AsWeiValue _) ts =
    (LENGTH ts = 1 /\ ty = BaseT (UintT 256) /\ is_numeric_type (HD ts)) /\
  well_typed_builtin_app ty (Concat n) ts =
    (2 <= LENGTH ts /\
     ((ty = BaseT (BytesT (Dynamic n)) /\ EVERY (\t. ?bd. t = BaseT (BytesT bd)) ts) \/
      (ty = BaseT (StringT n) /\ EVERY (\t. ?m. t = BaseT (StringT m)) ts))) /\
  well_typed_builtin_app ty (Slice n) ts =
    (LENGTH ts = 3 /\ EL 1 ts = BaseT (UintT 256) /\ EL 2 ts = BaseT (UintT 256) /\
     ((ty = BaseT (BytesT (Dynamic n)) /\ ?bd. HD ts = BaseT (BytesT bd)) \/
      (ty = BaseT (StringT n) /\ ?m. HD ts = BaseT (StringT m)))) /\
  well_typed_builtin_app ty (Uint2Str n) ts =
    (LENGTH ts = 1 /\ ty = BaseT (StringT n) /\ (?k. HD ts = BaseT (UintT k)) /\ 78 <= n) /\
  well_typed_builtin_app ty (MakeArray NONE bd) ts =
    (ty = TupleT ts /\ compatible_bound bd (LENGTH ts)) /\
  well_typed_builtin_app ty (MakeArray (SOME elem_ty) bd) ts =
    (ty = ArrayT elem_ty bd /\ compatible_bound bd (LENGTH ts) /\ EVERY ($= elem_ty) ts) /\
  well_typed_builtin_app ty Ceil ts =
    (LENGTH ts = 1 /\ HD ts = BaseT DecimalT /\ ty = BaseT (IntT 256)) /\
  well_typed_builtin_app ty Floor ts =
    (LENGTH ts = 1 /\ HD ts = BaseT DecimalT /\ ty = BaseT (IntT 256)) /\
  well_typed_builtin_app ty AddMod ts =
    (LENGTH ts = 3 /\ ty = BaseT (UintT 256) /\ EVERY ((=) (BaseT (UintT 256))) ts) /\
  well_typed_builtin_app ty MulMod ts =
    (LENGTH ts = 3 /\ ty = BaseT (UintT 256) /\ EVERY ((=) (BaseT (UintT 256))) ts) /\
  well_typed_builtin_app ty BlockHash ts = (ts = [BaseT (UintT 256)] /\ ty = BaseT (BytesT (Fixed 32))) /\
  well_typed_builtin_app ty BlobHash ts = (ts = [BaseT (UintT 256)] /\ ty = BaseT (BytesT (Fixed 32))) /\
  well_typed_builtin_app ty (Env item) ts = (ts = [] /\ ty = env_item_type item) /\
  well_typed_builtin_app ty (Acc item) ts =
    (LENGTH ts = 1 /\ HD ts = BaseT AddressT /\ ty = account_item_type item) /\
  well_typed_builtin_app ty MethodId ts =
    (LENGTH ts = 1 /\ ty = BaseT (BytesT (Fixed 4)) /\ is_bytes_or_string_type (HD ts)) /\
  well_typed_builtin_app ty ECRecover ts =
    (LENGTH ts = 4 /\ ty = BaseT AddressT /\ HD ts = BaseT (BytesT (Fixed 32)) /\
     EVERY (\t. t = BaseT (UintT 256) \/ t = BaseT (BytesT (Fixed 32))) (TL ts)) /\
  well_typed_builtin_app ty ECAdd ts =
    (LENGTH ts = 2 /\ ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EVERY (\t. t = ArrayT (BaseT (UintT 256)) (Fixed 2)) ts) /\
  well_typed_builtin_app ty ECMul ts =
    (LENGTH ts = 2 /\ ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EL 0 ts = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     EL 1 ts = BaseT (UintT 256)) /\
  well_typed_builtin_app ty PowMod256 ts =
    (ts = [BaseT (UintT 256); BaseT (UintT 256)] /\ ty = BaseT (UintT 256)) /\
  well_typed_builtin_app ty Abs ts = (ts = [ty] /\ is_numeric_type ty)
End

Definition well_formed_type_def:
  well_formed_type tenv ty = IS_SOME (evaluate_type tenv ty)
End

(* ===== Value-type/place typing for storage arrays and hashmaps ===== *)

Definition value_type_as_type_def:
  value_type_as_type (Type t) = SOME t /\
  value_type_as_type (HashMapT _ _) = NONE
End

Definition vtype_annotation_ok_def:
  vtype_annotation_ok (Type t) ann_ty = (ann_ty = t) /\
  vtype_annotation_ok (HashMapT _ _) ann_ty = (ann_ty = NoneT)
End

Definition subscript_type_ok_def:
  subscript_type_ok (ArrayT elem_ty _) idx_ty result_ty =
    (result_ty = elem_ty /\ is_int_type idx_ty) /\
  subscript_type_ok (TupleT ts) idx_ty result_ty =
    (is_int_type idx_ty /\ ts <> [] /\ EVERY ($= result_ty) ts) /\
  subscript_type_ok (BaseT _) _ _ = F /\
  subscript_type_ok (StructT _) _ _ = F /\
  subscript_type_ok (FlagT _) _ _ = F /\
  subscript_type_ok NoneT _ _ = F
End

Definition subscript_vtype_def:
  subscript_vtype (Type (ArrayT elem_ty _)) idx_ty =
    (if is_int_type idx_ty then SOME (Type elem_ty) else NONE) /\
  subscript_vtype (Type (TupleT ts)) idx_ty =
    (if is_int_type idx_ty /\ ts <> [] then
       case ts of [] => NONE | t::_ => if EVERY ($= t) ts then SOME (Type t) else NONE
     else NONE) /\
  subscript_vtype (HashMapT kt vt) idx_ty =
    (if idx_ty = kt then SOME vt else NONE) /\
  subscript_vtype _ _ = NONE
End

Definition attribute_type_def:
  attribute_type tenv (StructT sname) field_id =
    (case FLOOKUP tenv (string_to_num sname) of
       SOME (StructArgs fields) => ALOOKUP fields field_id
     | _ => NONE) /\
  attribute_type _ (BaseT _) _ = NONE /\
  attribute_type _ (TupleT _) _ = NONE /\
  attribute_type _ (ArrayT _ _) _ = NONE /\
  attribute_type _ (FlagT _) _ = NONE /\
  attribute_type _ NoneT _ = NONE
End

Definition attribute_type_ok_def:
  attribute_type_ok tenv ty field_id result_ty =
    (attribute_type tenv ty field_id = SOME result_ty)
End

(* ===== Runtime invariants ===== *)

Definition scope_well_typed_def:
  scope_well_typed (sc : scope) <=>
    !id entry. FLOOKUP sc id = SOME entry ==>
      value_has_type entry.type entry.value /\ well_formed_type_value entry.type
End

Definition imms_well_typed_def:
  imms_well_typed (imms : module_immutables) <=>
    !src_id_opt m id tv v.
      ALOOKUP imms src_id_opt = SOME m /\ FLOOKUP m id = SOME (tv, v) ==>
      value_has_type tv v /\ well_formed_type_value tv
End

Definition state_well_typed_def:
  state_well_typed st <=>
    EVERY scope_well_typed st.scopes /\
    EVERY (\(addr, mods). imms_well_typed mods) st.immutables
End

Datatype:
  fn_sig = <| param_types : type list;
              num_defaults : num;
              ret_ty : type |>
End

Datatype:
  typing_env = <|
    current_src     : num option;
    var_types       : (num |-> type);
    var_assignable  : (num |-> bool);
    bare_globals    : ((num option # num) |-> type);
    toplevel_vtypes : ((num option # num) |-> value_type);
    type_defs       : (num |-> type_args);
    fn_sigs         : ((num option # string) |-> fn_sig);
    flag_members    : ((num option # string) |-> string list)
  |>
End

Definition extend_local_def:
  extend_local env id typ assignable =
    env with <| var_types updated_by (flip FUPDATE (id, typ));
                var_assignable updated_by (flip FUPDATE (id, assignable)) |>
End

(* ===== Type builtin/conversion checks ===== *)

Definition valid_conversion_def:
  valid_conversion (BaseT (BytesT _)) (BaseT BoolT) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT BoolT) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT BoolT) = T /\
  valid_conversion (BaseT BoolT) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT BoolT) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (BytesT _)) (BaseT (BytesT _)) = T /\
  valid_conversion (BaseT (BytesT _)) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (BytesT _)) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT AddressT) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT AddressT) = T /\
  valid_conversion (FlagT _) (BaseT (IntT _)) = T /\
  valid_conversion (FlagT _) (BaseT (UintT _)) = T /\
  valid_conversion (BaseT (UintT _)) (FlagT _) = T /\
  valid_conversion (BaseT (IntT _)) (FlagT _) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT (BytesT _)) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT (BytesT _)) = T /\
  valid_conversion (BaseT (BytesT _)) (BaseT (StringT _)) = T /\
  valid_conversion (BaseT (StringT _)) (BaseT (StringT _)) = T /\
  valid_conversion (BaseT (StringT _)) (BaseT (BytesT _)) = T /\
  valid_conversion (BaseT (UintT _)) (BaseT DecimalT) = T /\
  valid_conversion (BaseT (IntT _)) (BaseT DecimalT) = T /\
  valid_conversion (BaseT DecimalT) (BaseT (IntT _)) = T /\
  valid_conversion (BaseT DecimalT) (BaseT (UintT _)) = T /\
  valid_conversion _ _ = F
End

Definition well_typed_type_builtin_args_def:
  well_typed_type_builtin_args Empty target_ty ts = (ts = []) /\
  well_typed_type_builtin_args MaxValue target_ty ts = (ts = [] /\ is_numeric_type target_ty) /\
  well_typed_type_builtin_args MinValue target_ty ts = (ts = [] /\ is_numeric_type target_ty) /\
  well_typed_type_builtin_args Epsilon target_ty ts = (ts = [] /\ target_ty = BaseT DecimalT) /\
  well_typed_type_builtin_args Convert target_ty ts =
    (LENGTH ts = 1 /\ valid_conversion (HD ts) target_ty) /\
  well_typed_type_builtin_args Extract32 target_ty ts =
    (LENGTH ts = 2 /\ (?bd. EL 0 ts = BaseT (BytesT bd)) /\ is_int_type (EL 1 ts) /\
     (?bt. target_ty = BaseT bt)) /\
  well_typed_type_builtin_args (AbiDecode _) target_ty ts =
    (LENGTH ts = 1 /\ ?bd. HD ts = BaseT (BytesT bd)) /\
  well_typed_type_builtin_args (AbiEncode _) target_ty ts =
    (ts <> [] /\ target_ty = TupleT ts)
End

Definition type_builtin_result_ok_def:
  type_builtin_result_ok (AbiEncode _) result_ty target_ty arg_tys =
    ((?n. result_ty = BaseT (BytesT (Dynamic n))) /\ target_ty = TupleT arg_tys) /\
  type_builtin_result_ok Empty result_ty target_ty arg_tys = (result_ty = target_ty) /\
  type_builtin_result_ok MaxValue result_ty target_ty arg_tys = (result_ty = target_ty) /\
  type_builtin_result_ok MinValue result_ty target_ty arg_tys = (result_ty = target_ty) /\
  type_builtin_result_ok Epsilon result_ty target_ty arg_tys = (result_ty = target_ty) /\
  type_builtin_result_ok Convert result_ty target_ty arg_tys = (result_ty = target_ty) /\
  type_builtin_result_ok Extract32 result_ty target_ty arg_tys = (result_ty = target_ty) /\
  type_builtin_result_ok (AbiDecode _) result_ty target_ty arg_tys = (result_ty = target_ty)
End

Definition raw_call_return_type_def:
  raw_call_return_type flags =
    if flags.rcf_revert_on_failure then
      if flags.rcf_max_outsize = 0 then NoneT
      else BaseT (BytesT (Dynamic flags.rcf_max_outsize))
    else
      if flags.rcf_max_outsize = 0 then BaseT BoolT
      else TupleT [BaseT BoolT; BaseT (BytesT (Dynamic flags.rcf_max_outsize))]
End

(* ===== Expressions, places, and targets ===== *)

Definition well_typed_expr_def:
  well_typed_expr env (Name ty id) =
    (FLOOKUP env.var_types (string_to_num id) = SOME ty) /\
  well_typed_expr env (BareGlobalName ty id) =
    (FLOOKUP env.bare_globals (env.current_src, string_to_num id) = SOME ty /\
     well_formed_type env.type_defs ty /\ ty <> NoneT) /\
  well_typed_expr env (TopLevelName ty (src_id_opt, id)) =
    (FLOOKUP env.toplevel_vtypes (src_id_opt, string_to_num id) = SOME (Type ty) /\
     well_formed_type env.type_defs ty /\ ty <> NoneT) /\
  well_typed_expr env (FlagMember ty (src_id_opt, fid) mid) =
    (ty = FlagT fid /\ well_formed_type env.type_defs ty /\
     ?ls. FLOOKUP env.flag_members (src_id_opt, fid) = SOME ls /\ MEM mid ls) /\
  well_typed_expr env (IfExp ty cond e1 e2) =
    (well_typed_expr env cond /\ well_typed_expr env e1 /\ well_typed_expr env e2 /\
     expr_type cond = BaseT BoolT /\ expr_type e1 = ty /\ expr_type e2 = ty /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Literal ty l) =
    (well_typed_literal ty l /\ well_formed_type env.type_defs ty) /\
  well_typed_expr env (StructLit ty nsid kes) =
    (well_typed_named_exprs env kes /\ well_formed_type env.type_defs ty /\
     ?id args. ty = StructT id /\ SND nsid = id /\
       FLOOKUP env.type_defs (string_to_num id) = SOME (StructArgs args) /\
       MAP FST kes = MAP FST args /\ MAP (expr_type o SND) kes = MAP SND args) /\
  well_typed_expr env (Subscript ty e1 e2) =
    (well_typed_expr env e2 /\ well_formed_type env.type_defs ty /\
     ((well_typed_expr env e1 /\ subscript_type_ok (expr_type e1) (expr_type e2) ty) \/
      (?vt. type_place_expr env e1 = SOME vt /\
            subscript_vtype vt (expr_type e2) = SOME (Type ty)))) /\
  well_typed_expr env (Attribute ty e id) =
    (well_typed_expr env e /\ attribute_type_ok env.type_defs (expr_type e) id ty /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Builtin ty blt es) =
    (well_typed_exprs env es /\ well_typed_builtin_app ty blt (MAP expr_type es) /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (TypeBuiltin ty tb target_ty es) =
    (well_typed_exprs env es /\ well_formed_type env.type_defs ty /\
     type_builtin_result_ok tb ty target_ty (MAP expr_type es) /\
     well_typed_type_builtin_args tb target_ty (MAP expr_type es)) /\
  well_typed_expr env (Pop ty tgt) =
    (?bd. type_place_target env tgt = SOME (Type (ArrayT ty bd))) /\
  well_typed_expr env (Call ty (IntCall (src_id_opt, fn_name)) args drv) =
    (well_typed_exprs env args /\ well_typed_opt env drv /\ well_formed_type env.type_defs ty /\
     ?sig. FLOOKUP env.fn_sigs (src_id_opt, fn_name) = SOME sig /\
       ty = sig.ret_ty /\ LENGTH args <= LENGTH sig.param_types /\
       LENGTH sig.param_types - sig.num_defaults <= LENGTH args /\
       MAP expr_type args = TAKE (LENGTH args) sig.param_types) /\
  well_typed_expr env (Call ty (ExtCall is_static (_, arg_types, ret_ty)) args drv) =
    (well_typed_exprs env args /\ well_typed_opt env drv /\ well_formed_type env.type_defs ty /\
     ty = ret_ty /\
     (if is_static then MAP expr_type args = BaseT AddressT :: arg_types
      else MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_types) /\
     (!e. drv = SOME e ==> expr_type e = ret_ty)) /\
  well_typed_expr env (Call ty Send args drv) =
    (well_typed_exprs env args /\ drv = NONE /\ LENGTH args = 2 /\ ty = NoneT /\
     HD (MAP expr_type args) = BaseT AddressT /\ EL 1 (MAP expr_type args) = BaseT (UintT 256)) /\
  well_typed_expr env (Call ty (RawCallTarget flags) args drv) =
    (well_typed_exprs env args /\ drv = NONE /\ ty = raw_call_return_type flags /\
     flags.rcf_max_outsize < dimword(:256) /\ LENGTH args = 3 /\
     EL 0 (MAP expr_type args) = BaseT AddressT /\
     (?bd. EL 1 (MAP expr_type args) = BaseT (BytesT bd)) /\
     EL 2 (MAP expr_type args) = BaseT (UintT 256)) /\
  well_typed_expr env (Call ty RawLog args drv) =
    (well_typed_exprs env args /\ drv = NONE /\ ty = NoneT /\ LENGTH args = 2 /\
     (?bd. EL 0 (MAP expr_type args) = ArrayT (BaseT (BytesT (Fixed 32))) bd) /\
     (?bd'. EL 1 (MAP expr_type args) = BaseT (BytesT bd'))) /\
  well_typed_expr env (Call ty RawRevert args drv) =
    (well_typed_exprs env args /\ drv = NONE /\ ty = NoneT /\ LENGTH args = 1 /\
     (?bd. HD (MAP expr_type args) = BaseT (BytesT bd))) /\
  well_typed_expr env (Call ty SelfDestructTarget args drv) =
    (well_typed_exprs env args /\ drv = NONE /\ ty = NoneT /\ LENGTH args = 1 /\
     HD (MAP expr_type args) = BaseT AddressT) /\
  well_typed_expr env (Call ty (CreateTarget kind rof) args drv) =
    (well_typed_exprs env args /\ drv = NONE /\ ty = BaseT AddressT /\ LENGTH args >= 2 /\
     HD (MAP expr_type args) = BaseT AddressT /\ LAST (MAP expr_type args) = BaseT (UintT 256)) /\

  type_place_expr env (TopLevelName ty (src_id_opt, id)) =
    (case FLOOKUP env.toplevel_vtypes (src_id_opt, string_to_num id) of
     | SOME vt => if vtype_annotation_ok vt ty then SOME vt else NONE
     | NONE => NONE) /\
  type_place_expr env (Subscript ty e1 e2) =
    (if well_typed_expr env e2 then
       case type_place_expr env e1 of
       | SOME vt =>
           (case subscript_vtype vt (expr_type e2) of
            | SOME vt' => if vtype_annotation_ok vt' ty then SOME vt' else NONE
            | NONE => NONE)
       | NONE => NONE
     else NONE) /\
  type_place_expr env _ = NONE /\

  type_place_target env (NameTarget id) =
    (let n = string_to_num id in
     case (FLOOKUP env.var_types n, FLOOKUP env.var_assignable n) of
     | (SOME ty, SOME T) => SOME (Type ty)
     | _ => NONE) /\
  type_place_target env (BareGlobalNameTarget id) =
    (case FLOOKUP env.bare_globals (env.current_src, string_to_num id) of
     | SOME ty => SOME (Type ty) | NONE => NONE) /\
  type_place_target env (TopLevelNameTarget (src_id_opt, id)) =
    FLOOKUP env.toplevel_vtypes (src_id_opt, string_to_num id) /\
  type_place_target env (SubscriptTarget tgt e) =
    (if well_typed_expr env e then
       case type_place_target env tgt of
       | SOME vt => subscript_vtype vt (expr_type e)
       | NONE => NONE
     else NONE) /\
  type_place_target env (AttributeTarget tgt id) =
    (case type_place_target env tgt of
     | SOME (Type tgt_ty) =>
         (case attribute_type env.type_defs tgt_ty id of
          | SOME ty => SOME (Type ty)
          | NONE => NONE)
     | _ => NONE) /\

  well_typed_exprs env [] = T /\
  well_typed_exprs env (e::es) = (well_typed_expr env e /\ well_typed_exprs env es) /\
  well_typed_opt env NONE = T /\
  well_typed_opt env (SOME e) = well_typed_expr env e /\
  well_typed_named_exprs env [] = T /\
  well_typed_named_exprs env ((k,e)::kes) =
    (well_typed_expr env e /\ well_typed_named_exprs env kes)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (_, e) => expr_size e
    | INR (INL (_, e)) => expr_size e
    | INR (INR (INL (_, tgt))) => base_assignment_target_size tgt
    | INR (INR (INR (INL (_, es)))) => expr4_size es
    | INR (INR (INR (INR (INL (_, opt))))) => expr3_size opt
    | INR (INR (INR (INR (INR (_, kes))))) => expr1_size kes)`
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

Definition well_typed_target_def:
  well_typed_target env bt ty = (type_place_target env bt = SOME (Type ty))
End

Definition well_typed_atarget_def:
  well_typed_atarget env (BaseTarget bt) ty = well_typed_target env bt ty /\
  well_typed_atarget env (TupleTarget tgts) ty =
    (?tys. LIST_REL (\tgt ty. well_typed_atarget env tgt ty) tgts tys /\ ty = TupleT tys)
Termination
  WF_REL_TAC `measure (\(_,t,_). assignment_target_size t)`
End

Definition well_typed_iterator_def:
  well_typed_iterator env typ (Array e) =
    (well_typed_expr env e /\ ?bd. expr_type e = ArrayT typ bd) /\
  well_typed_iterator env typ (Range e1 e2) =
    (well_typed_expr env e1 /\ well_typed_expr env e2 /\
     is_int_type typ /\ expr_type e1 = typ /\ expr_type e2 = typ)
End

(* ===== Executable statement typing ===== *)

Definition type_stmt_def:
  type_stmt env ret_ty Pass = SOME env /\
  type_stmt env ret_ty Continue = SOME env /\
  type_stmt env ret_ty Break = SOME env /\
  type_stmt env ret_ty (Expr e) =
    (if well_typed_expr env e then SOME env else NONE) /\
  type_stmt env ret_ty (Return NONE) =
    (if ret_ty = NoneT then SOME env else NONE) /\
  type_stmt env ret_ty (Return (SOME e)) =
    (if well_typed_expr env e /\ expr_type e = ret_ty /\ ret_ty <> NoneT then SOME env else NONE) /\
  type_stmt env ret_ty (Raise RaiseBare) = SOME env /\
  type_stmt env ret_ty (Raise RaiseUnreachable) = SOME env /\
  type_stmt env ret_ty (Raise (RaiseReason e)) =
    (if well_typed_expr env e /\ (?n. expr_type e = BaseT (StringT n)) then SOME env else NONE) /\
  type_stmt env ret_ty (Assert e AssertBare) =
    (if well_typed_expr env e /\ expr_type e = BaseT BoolT then SOME env else NONE) /\
  type_stmt env ret_ty (Assert e AssertUnreachable) =
    (if well_typed_expr env e /\ expr_type e = BaseT BoolT then SOME env else NONE) /\
  type_stmt env ret_ty (Assert e (AssertReason se)) =
    (if well_typed_expr env e /\ well_typed_expr env se /\ expr_type e = BaseT BoolT /\
        (?n. expr_type se = BaseT (StringT n)) then SOME env else NONE) /\
  type_stmt env ret_ty (Log id es) =
    (if well_typed_exprs env es then SOME env else NONE) /\
  type_stmt env ret_ty (AnnAssign id typ e) =
    (if well_typed_expr env e /\ well_formed_type env.type_defs typ /\ expr_type e = typ /\
        string_to_num id NOTIN FDOM env.var_types
     then SOME (extend_local env (string_to_num id) typ T)
     else NONE) /\
  type_stmt env ret_ty (Append bt e) =
    (case type_place_target env bt of
     | SOME (Type (ArrayT elem_ty bd)) =>
         if well_typed_expr env e /\ expr_type e = elem_ty then SOME env else NONE
     | _ => NONE) /\
  type_stmt env ret_ty (Assign tgt e) =
    (if well_typed_atarget env tgt (expr_type e) /\ well_typed_expr env e then SOME env else NONE) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) =
    (if well_typed_target env bt ty /\ well_typed_expr env e /\ well_formed_type env.type_defs ty /\
        well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn
     then SOME env else NONE) /\
  type_stmt env ret_ty (If e ss1 ss2) =
    (if well_typed_expr env e /\ expr_type e = BaseT BoolT /\
        IS_SOME (type_stmts env ret_ty ss1) /\ IS_SOME (type_stmts env ret_ty ss2)
     then SOME env else NONE) /\
  type_stmt env ret_ty (For id typ it n body) =
    (if well_formed_type env.type_defs typ /\ well_typed_iterator env typ it /\
        string_to_num id NOTIN FDOM env.var_types /\
        IS_SOME (type_stmts (extend_local env (string_to_num id) typ F) ret_ty body)
     then SOME env else NONE) /\
  type_stmts env ret_ty [] = SOME env /\
  type_stmts env ret_ty (s::ss) =
    (case type_stmt env ret_ty s of NONE => NONE | SOME env' => type_stmts env' ret_ty ss)
Termination
  WF_REL_TAC `measure (\x.
    case x of INL(_,_,t) => stmt_size t
            | INR(_,_,ts) => list_size stmt_size ts)`
End

Definition well_typed_stmt_def:
  well_typed_stmt env ret_ty s = IS_SOME (type_stmt env ret_ty s)
End

Definition well_typed_stmts_def:
  well_typed_stmts env ret_ty ss = IS_SOME (type_stmts env ret_ty ss)
End

(* ===== Global consistency predicates ===== *)

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

Definition env_consistent_def:
  env_consistent env cx st <=>
    env.type_defs = get_tenv cx /\
    env.current_src = current_module cx /\
    fn_sigs_consistent env.fn_sigs cx /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> IS_SOME (lookup_scopes id st.scopes)) /\
    (!id ty entry.
       FLOOKUP env.var_types id = SOME ty /\ lookup_scopes id st.scopes = SOME entry ==>
       evaluate_type (get_tenv cx) ty = SOME entry.type) /\
    (!id. FLOOKUP env.var_assignable id = SOME T ==> IS_SOME (FLOOKUP env.var_types id)) /\
    (!id. FLOOKUP env.var_assignable id = SOME T ==>
       ?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable) /\
    (!src id ty ts. FLOOKUP env.bare_globals (src,id) = SOME ty /\ get_module_code cx src = SOME ts ==>
       FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
       is_immutable_decl id ts /\ ty <> NoneT) /\
    (!id ty. FLOOKUP env.bare_globals (env.current_src,id) = SOME ty ==>
       IS_SOME (FLOOKUP (get_source_immutables env.current_src
         (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id)) /\
    (!id ty tv v.
       FLOOKUP env.bare_globals (env.current_src,id) = SOME ty /\
       FLOOKUP (get_source_immutables env.current_src
         (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!src id ty ts.
       FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ get_module_code cx src = SOME ts ==>
       (!is_transient typ id_str.
          find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==> F) /\
       (find_var_decl_by_num id ts = NONE ==>
         !tv v. FLOOKUP (get_source_immutables src
           (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
         evaluate_type (get_tenv cx) ty = SOME tv)) /\
    (!src id kt vt ts.
       FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) /\ get_module_code cx src = SOME ts ==>
       ?is_transient id_str.
          find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str)) /\
    (!src fid ls.
       FLOOKUP env.flag_members (src, fid) = SOME ls ==>
       ?ts. get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) = SOME (FlagArgs (LENGTH ls)))
End

Definition defaults_env_def:
  defaults_env env = env with <| var_types := FEMPTY; var_assignable := FEMPTY |>
End

Definition functions_well_typed_def:
  functions_well_typed cx <=>
    !fn_sigs bare_globals toplevel_vtypes flag_members.
      fn_sigs_consistent fn_sigs cx /\
      (!src id ty ts. FLOOKUP bare_globals (src,id) = SOME ty /\ get_module_code cx src = SOME ts ==>
         FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
         is_immutable_decl id ts /\ ty <> NoneT) /\
      (!src id vt ts.
         FLOOKUP toplevel_vtypes (src,id) = SOME vt /\ get_module_code cx src = SOME ts ==>
         ((?ty. vt = Type ty /\
             ((!is_transient typ id_str.
                 find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
              (!is_transient kt hv id_str.
                 find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt hv,id_str) ==> F) /\
              (find_var_decl_by_num id ts = NONE ==> IS_SOME (evaluate_type (get_tenv cx) ty)))) \/
          (?kt hv. vt = HashMapT kt hv /\
             ?is_transient id_str.
               find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt hv,id_str)))) /\
      (!src fid ls.
         FLOOKUP flag_members (src,fid) = SOME ls ==>
         ?ts. get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
              FLOOKUP (get_tenv cx) (string_to_num fid) = SOME (FlagArgs (LENGTH ls))) ==>
      !src_id_opt fn ts fm nr args dflts ret body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,args,dflts,ret,body) ==>
        (nr ==> cx.nonreentrant_slot <> NONE) /\
        ?env_body ret_tv env_after.
          env_body.current_src = src_id_opt /\
          env_body.type_defs = get_tenv cx /\
          env_body.fn_sigs = fn_sigs /\
          env_body.bare_globals = bare_globals /\
          env_body.toplevel_vtypes = toplevel_vtypes /\
          env_body.flag_members = flag_members /\
          evaluate_type (get_tenv cx) ret = SOME ret_tv /\
          type_stmts env_body ret body = SOME env_after /\
          well_typed_exprs (defaults_env env_body) dflts /\
          (!id typ. MEM (id,typ) args ==>
             FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
             FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
          (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
             ?id. MEM (id,ty) args /\ n = string_to_num id) /\
          (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
             ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
          MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
End

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

Definition account_well_typed_def:
  account_well_typed (a : account_state) <=>
    a.balance < 2 ** 256 /\ LENGTH a.code <= 24576
End

Definition accounts_well_typed_def:
  accounts_well_typed acc <=>
    !addr. account_well_typed (lookup_account addr acc)
End

Definition toplevel_value_typed_def:
  (toplevel_value_typed (Value v) tyv <=> value_has_type tyv v) /\
  (toplevel_value_typed (ArrayRef _ _ elem_tv bd) tyv <=> tyv = ArrayTV elem_tv bd) /\
  (toplevel_value_typed (HashMapRef _ _ _ _) tyv <=> tyv = NoneTV)
End

