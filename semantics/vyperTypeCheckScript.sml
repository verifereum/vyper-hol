(*
 * vyperTypeCheckScript.sml
 *
 * Type system definitions and type soundness proof infrastructure.
 *
 * TOP-LEVEL:
 *   typing_env          : static type environment (var_types, global_types, etc.)
 *   well_typed_expr     : typing_env → expr → bool (static type consistency)
 *   env_consistent      : typing_env → cx → st → bool (env matches runtime state)
 *   state_well_typed    : evaluation_state → bool (runtime values satisfy stored types)
 *   satisfies_type      : value → type_value → bool (value matches resolved type)
 *   type_preservation   : well_typed + consistent + eval ⇒ preserves types (CHEATED)
 *
 * Operation-level helpers (proved):
 *   evaluate_literal_satisfies_type, bounded_int_op_unsigned/signed,
 *   evaluate_binop_add_uint, evaluate_builtin_bop_add_uint
 *
 * State helpers (proved):
 *   lookup_scopes_well_typed, lookup_scopes_val_well_typed
 *
 * PROOF STATUS:
 *   type_preservation: Name and Literal cases proved by induction.
 *   11 cases cheated (BareGlobalName, TopLevelName, FlagMember, IfExp,
 *   StructLit, Subscript, Attribute, Builtin, TypeBuiltin, Pop, Call).
 *   Induction structure validated — IH provides env_consistent for
 *   intermediate states, enabling compositional proofs for IfExp etc.
 *)

Theory vyperTypeCheck
Ancestors
  vyperAST vyperValue vyperValueOperation vyperMisc
  vyperInterpreter vyperState vyperContext

(* ===== Type Classification Helpers ===== *)

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

(* ===== satisfies_type: value matches resolved type ===== *)

Definition satisfies_type_def:
  (* base types *)
  satisfies_type NoneV NoneTV = T /\
  satisfies_type (BoolV _) (BaseTV BoolT) = T /\
  satisfies_type (IntV n) (BaseTV (UintT k)) =
    within_int_bound (Unsigned k) n /\
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
  satisfies_type (ArrayV (DynArrayV vs)) (ArrayTV tv (Dynamic m)) =
    (LENGTH vs <= m /\ all_satisfy_type vs tv) /\
  satisfies_type (ArrayV (SArrayV al)) (ArrayTV tv (Fixed m)) =
    (ALL_DISTINCT (MAP FST al) /\
     EVERY (\(k,_). k < m) al /\
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
    ∀id tv v. FLOOKUP sc id = SOME (tv, v) ⇒ satisfies_type v tv
End

Definition imms_well_typed_def:
  imms_well_typed (imms : module_immutables) ⇔
    ∀src_id_opt m id tv v.
      ALOOKUP imms src_id_opt = SOME m ∧
      FLOOKUP m id = SOME (tv, v) ⇒
      satisfies_type v tv
End

Definition state_well_typed_def:
  state_well_typed st ⇔
    EVERY scope_well_typed st.scopes ∧
    EVERY (λ(addr, mods). imms_well_typed mods) st.immutables
End

(* Helper: looking up a variable in well-typed scopes gives a well-typed value *)
Theorem lookup_scopes_well_typed:
  !scopes id tv v.
    EVERY scope_well_typed scopes /\
    lookup_scopes id scopes = SOME (tv, v) ==>
    satisfies_type v tv
Proof
  Induct >> simp[lookup_scopes_def] >>
  rpt gen_tac >>
  Cases_on `FLOOKUP h id` >> fs[] >>
  strip_tac >> fs[scope_well_typed_def] >>
  res_tac
QED

(* Helper: lookup_scopes_val returns a value that satisfies some type_value *)
Theorem lookup_scopes_val_well_typed:
  !scopes id v.
    EVERY scope_well_typed scopes /\
    lookup_scopes_val id scopes = SOME v ==>
    ?tv. lookup_scopes id scopes = SOME (tv, v) /\
         satisfies_type v tv
Proof
  Induct >> simp[lookup_scopes_def, lookup_scopes_val_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP h id` >> gvs[] >>
  Cases_on `x` >> simp[] >>
  fs[scope_well_typed_def] >> res_tac
QED

(* ===== Type soundness roadmap ===== *)
(*
 * The overall goal is to show that well-typed programs never raise TypeError.
 * The proof proceeds in phases:
 *
 * Phase 2: Operation-level lemmas
 *   - evaluate_literal produces values satisfying the literal's type
 *   - evaluate_binop preserves types when inputs satisfy their types
 *   - evaluate_builtin preserves types
 *   These are independent of eval_expr and can be proved first.
 *
 * Phase 3-5: Type preservation (the workhorse)
 *   If state_well_typed st, and eval_expr cx e st succeeds with (Value v, st'),
 *   then satisfies_type v tv (where tv = evaluate_type ... (expr_type e))
 *   and state_well_typed st'.
 *   Proved by structural induction on e, one helper lemma per constructor.
 *
 * Phase 6: No-TypeError
 *   Every TypeError raise site in the interpreter is guarded by a type check
 *   that succeeds when state_well_typed holds and the program is well-formed.
 *   Derived from type preservation.
 *)

(* Phase 2: Operation-level helpers (TODO) *)

Theorem evaluate_literal_satisfies_type:
  ∀ty l tv.
    well_typed_literal ty l ∧
    evaluate_type tenv ty = SOME tv ⇒
    satisfies_type (evaluate_literal l) tv
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ty` >> gvs[well_typed_literal_def] >>
  Cases_on `l` >> Cases_on `b` >>
  gvs[well_typed_literal_def] >>
  gvs[Once evaluate_type_def] >>
  REWRITE_TAC[evaluate_literal_def] >>
  REWRITE_TAC[satisfies_type_def] >>
  simp[]
QED

(* Phase 2: bounded_int_op result satisfies the bound's type *)
Theorem bounded_int_op_unsigned:
  !k r v.
    bounded_int_op (Unsigned k) r = INL v ==>
    satisfies_type v (BaseTV (UintT k))
Proof
  rw[bounded_int_op_def] >> gvs[] >>
  REWRITE_TAC[satisfies_type_def] >> simp[]
QED

Theorem bounded_int_op_signed:
  !k r v.
    bounded_int_op (Signed k) r = INL v ==>
    satisfies_type v (BaseTV (IntT k))
Proof
  rw[bounded_int_op_def] >> gvs[] >>
  REWRITE_TAC[satisfies_type_def] >> simp[]
QED

(* Phase 2: evaluate_binop Add on uint preserves satisfies_type *)
Theorem evaluate_binop_add_uint:
  !k tv v1 v2 r.
    evaluate_binop (Unsigned k) tv Add v1 v2 = INL r /\
    satisfies_type v1 (BaseTV (UintT k)) /\
    satisfies_type v2 (BaseTV (UintT k)) ==>
    satisfies_type r (BaseTV (UintT k))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v1` >> Cases_on `v2` >>
  gvs[satisfies_type_def] >>
  gvs[Once evaluate_binop_def] >>
  metis_tac[bounded_int_op_unsigned]
QED

(* Phase 2: evaluate_builtin Bop Add on uint preserves satisfies_type *)
Theorem evaluate_builtin_bop_add_uint:
  !cx acc k v1 v2 r.
    evaluate_builtin cx acc (BaseT (UintT k)) (Bop Add) [v1; v2] = INL r /\
    satisfies_type v1 (BaseTV (UintT k)) /\
    satisfies_type v2 (BaseTV (UintT k)) ==>
    satisfies_type r (BaseTV (UintT k))
Proof
  rw[evaluate_builtin_def, type_to_int_bound_def, LET_THM] >>
  metis_tac[evaluate_binop_add_uint]
QED

(* ===== Static typing environment ===== *)
(*
 * typing_env captures the static type information a type checker would produce.
 * It maps variable names to their declared (syntactic) types.
 * This is state-independent — it doesn't change during evaluation.
 *
 * env_consistent links the typing_env to the runtime state:
 * for every variable in scope, the stored type_value equals
 * evaluate_type of the declared type.
 *)

Datatype:
  typing_env = <|
    var_types : (num |-> type);
    global_types : (num |-> type);
    toplevel_types : ((num option # num) |-> type);
    type_defs : (num |-> type_args);
  |>
End

(* env_consistent: typing env matches runtime state *)
Definition env_consistent_def:
  env_consistent env cx st <=>
    env.type_defs = get_tenv cx /\
    (!id ty tv v.
       FLOOKUP env.var_types id = SOME ty /\
       lookup_scopes id st.scopes = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!id ty tv v.
       FLOOKUP env.global_types id = SOME ty /\
       FLOOKUP (get_source_immutables (current_module cx)
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv)
End

(* ===== well_typed_expr: state-independent AST annotation consistency ===== *)

Definition well_typed_expr_def:
  well_typed_expr env (Name ty id) =
    (FLOOKUP env.var_types (string_to_num id) = SOME ty) /\
  well_typed_expr env (BareGlobalName ty id) =
    (FLOOKUP env.global_types (string_to_num id) = SOME ty) /\
  well_typed_expr env (TopLevelName ty (src_id_opt, id)) =
    (FLOOKUP env.toplevel_types (src_id_opt, string_to_num id) = SOME ty) /\
  well_typed_expr env (FlagMember ty _ _) =
    is_flag_type ty /\
  well_typed_expr env (IfExp ty cond e1 e2) =
    (well_typed_expr env cond /\
     well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     expr_type cond = BaseT BoolT /\
     expr_type e1 = ty /\ expr_type e2 = ty) /\
  well_typed_expr env (Literal ty l) =
    well_typed_literal ty l /\
  well_typed_expr env (StructLit ty _ kes) =
    (well_typed_named_exprs env kes /\
     is_struct_type ty) /\
  well_typed_expr env (Subscript ty e1 e2) =
    (well_typed_expr env e1 /\
     well_typed_expr env e2 /\
     subscript_type_ok (expr_type e1) (expr_type e2) ty) /\
  well_typed_expr env (Attribute ty e id) =
    (well_typed_expr env e /\
     attribute_type_ok env.type_defs (expr_type e) id ty) /\
  well_typed_expr env (Builtin ty blt es) =
    (well_typed_exprs env es /\
     well_typed_builtin_app ty blt (MAP expr_type es)) /\
  well_typed_expr env (TypeBuiltin ty _ target_ty es) =
    (well_typed_exprs env es /\
     well_formed_type env.type_defs ty /\
     well_formed_type env.type_defs target_ty) /\
  well_typed_expr env (Pop ty tgt) =
    (well_typed_target env tgt /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Call ty (IntCall _) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     well_formed_type env.type_defs ty) /\
  well_typed_expr env (Call ty (ExtCall _ (_, arg_types, ret_ty)) args drv) =
    (well_typed_exprs env args /\
     well_typed_opt env drv /\
     ty = ret_ty) /\
  well_typed_expr env (Call ty Send args drv) =
    (well_typed_exprs env args /\
     LENGTH args = 2 /\ ty = NoneT) /\
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

(* ===== Type preservation by induction ===== *)
(*
 * The theorem: if the expression is well-typed (statically) and the
 * typing environment is consistent with the runtime state, then
 * evaluation preserves types and the state invariant.
 *
 * env_consistent is the bridge: it says the typing_env matches
 * what's actually stored in scopes/immutables.
 *)

Theorem type_preservation:
  !e cx env st v st' tv.
    well_typed_expr env e /\
    env_consistent env cx st /\
    state_well_typed st /\
    eval_expr cx e st = (INL (Value v), st') /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    satisfies_type v tv /\ state_well_typed st' /\ env_consistent env cx st'
Proof
  Induct >> rpt gen_tac >>
  simp[expr_type_def, well_typed_expr_def] >> strip_tac
  (* Name: eval_expr doesn't change state, so st' = st *)
  >- (qpat_x_assum `eval_expr _ _ _ = _`
        (mp_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
      simp[bind_def, get_scopes_def, lift_option_type_def,
           return_def, LET_THM] >>
      Cases_on `lookup_scopes_val (string_to_num s) st.scopes` >>
      simp[return_def, raise_def] >> strip_tac >> rw[] >>
      `EVERY scope_well_typed st.scopes` by fs[state_well_typed_def] >>
      imp_res_tac lookup_scopes_val_well_typed >>
      fs[env_consistent_def] >>
      first_x_assum drule >> disch_then drule >> gvs[])
  (* BareGlobalName *)
  >- cheat
  (* TopLevelName *)
  >- cheat
  (* FlagMember *)
  >- cheat
  (* IfExp *)
  >- cheat
  (* Literal *)
  >- (gvs[Once evaluate_def, return_def] >>
      fs[env_consistent_def] >>
      metis_tac[evaluate_literal_satisfies_type])
  (* StructLit *)
  >- cheat
  (* Subscript *)
  >- cheat
  (* Attribute *)
  >- cheat
  (* Builtin *)
  >- cheat
  (* TypeBuiltin *)
  >- cheat
  (* Pop *)
  >- cheat
  (* Call *)
  >- cheat
QED
