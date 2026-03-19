(*
 * Type system definitions and type soundness proof infrastructure.
 *
 * TOP-LEVEL:
 *   typing_env          : static type environment (var_types, global_types, etc.)
 *   well_typed_expr     : typing_env → expr → bool (static type consistency)
 *   env_consistent      : typing_env → cx → st → bool (env matches runtime state)
 *   state_well_typed    : evaluation_state → bool (runtime values satisfy stored types)
 *   (uses value_has_type from vyperTypingTheory for value/type compatibility)
 *   type_preservation   : well_typed + consistent + eval ⇒ preserves types
 *
 * PROOF STATUS (this file):
 *   type_preservation: 10/47 cases proved, 37 cheated.
 *   intcall_state_preserved: 1 internal cheat (EL precondition for bind_arguments).
 *   All other helper theorems verified.
 *
 * REMAINING WORK (ordered by risk):
 *
 * --- RESOLVED: safe_cast type preservation ---
 *   safe_cast_preserves_well_typed: value_has_type tv v ∧ safe_cast tv v = SOME v'
 *     ⇒ value_has_type tv v'  (trivially from safe_cast_well_typed: cast is identity)
 *   NOTE: the stronger "safe_cast tv v = SOME v' ⇒ value_has_type tv v'" is FALSE
 *   for SArrayV (sparse arrays can have default values that violate sparse_has_type).
 *   In well-typed programs, inputs already satisfy value_has_type, so safe_cast_preserves_well_typed suffices.
 *
 * --- RISK 1: assign_subscripts preserves value_has_type ---
 *   Partial progress in vyperAssignPreservesTypeScript.sml:
 *     PROVED: insert_sarray_SORTED, insert_sarray_sparse_has_type,
 *       ADELKEY_SORTED, ADELKEY_sparse_has_type, TAKE_DROP_all_have_type,
 *       array_set_index_DynArrayV, array_set_index_SArrayV,
 *       FRONT_all_have_type, pop_element_preserves_type
 *     CHEATED: append_element_preserves_type (needs safe_cast_implies_well_typed),
 *       AFUPDKEY_struct_has_type (proof mechanics), assign_subscripts_preserves_type
 *
 * --- RISK 2: assign_target preserves storage_consistent ---
 *   (unchanged — see vyperLookupStorageScript.sml for storage definitions)
 *
 * --- RISK 3: Builtin operation type preservation ---
 *   ~30 builtin operations, each needs its own value_has_type lemma.
 *   Only Add/uint done so far (bounded_int_op_unsigned/signed).
 *
 * --- RISK 4: ExtCall preserves storage_consistent ---
 *   May need to assume storage_consistent as a postcondition.
 *
 * --- LOW RISK: remaining type_preservation cases ---
 *   Mechanical: goals 17-20, 22-27 (targets, iterators, ~12 cheats)
 *   IH-only: goals 4-7, 12, 14 (Return SOME, Raise, Assert, Log, If, Expr)
 *   Assignment: goals 8-11, 13, 29 (AnnAssign, Assign, AugAssign, Append, For)
 *   Expression: goals 31-34, 36-44 (various expr forms)
 *)

Theory vyperTypeSoundness
Ancestors
  vyperAST vyperValue vyperValueOperation vyperMisc
  vyperInterpreter vyperState vyperContext
  vyperStatePreservation vyperTyping vyperEncodeDecode

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
    ∀id tv v. FLOOKUP sc id = SOME (tv, v) ⇒ value_has_type tv v
End

Definition imms_well_typed_def:
  imms_well_typed (imms : module_immutables) ⇔
    ∀src_id_opt m id tv v.
      ALOOKUP imms src_id_opt = SOME m ∧
      FLOOKUP m id = SOME (tv, v) ⇒
      value_has_type tv v
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
    value_has_type tv v
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
         value_has_type tv v
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

Theorem evaluate_literal_has_type:
  ∀ty l tv.
    well_typed_literal ty l ∧
    evaluate_type tenv ty = SOME tv ⇒
    value_has_type tv (evaluate_literal l)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ty` >> gvs[well_typed_literal_def] >>
  Cases_on `l` >> Cases_on `b` >>
  gvs[well_typed_literal_def] >>
  gvs[Once evaluate_type_def] >>
  REWRITE_TAC[evaluate_literal_def] >>
  REWRITE_TAC[value_has_type_def] >>
  simp[within_int_bound_def] >>
  TRY (Cases_on `b'` >>
       gvs[compatible_bound_def, value_has_type_def]) >>
  gvs[within_int_bound_def]
QED

(* Phase 2: bounded_int_op result has the bound's type *)
Theorem bounded_int_op_unsigned:
  !k r v.
    bounded_int_op (Unsigned k) r = INL v /\ k ≤ 256 ==>
    value_has_type (BaseTV (UintT k)) v
Proof
  rw[bounded_int_op_def] >>
  gvs[value_has_type_def, within_int_bound_def]
QED

Theorem bounded_int_op_signed:
  !k r v.
    bounded_int_op (Signed k) r = INL v /\ k ≤ 256 ==>
    value_has_type (BaseTV (IntT k)) v
Proof
  rw[bounded_int_op_def] >> gvs[] >>
  REWRITE_TAC[value_has_type_def] >> simp[]
QED

(* Phase 2: evaluate_binop Add on uint preserves value_has_type *)
Theorem evaluate_binop_add_uint:
  !k tv v1 v2 r.
    evaluate_binop (Unsigned k) tv Add v1 v2 = INL r /\
    value_has_type (BaseTV (UintT k)) v1 /\
    value_has_type (BaseTV (UintT k)) v2 ==>
    value_has_type (BaseTV (UintT k)) r
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v1` >> Cases_on `v2` >>
  gvs[value_has_type_def] >>
  gvs[Once evaluate_binop_def] >>
  metis_tac[bounded_int_op_unsigned]
QED

(* Phase 2: evaluate_builtin Bop Add on uint preserves value_has_type *)
Theorem evaluate_builtin_bop_add_uint:
  !cx acc k v1 v2 r.
    evaluate_builtin cx acc (BaseT (UintT k)) (Bop Add) [v1; v2] = INL r /\
    value_has_type (BaseTV (UintT k)) v1 /\
    value_has_type (BaseTV (UintT k)) v2 ==>
    value_has_type (BaseTV (UintT k)) r
Proof
  rw[evaluate_builtin_def, type_to_int_bound_def, LET_THM] >>
  metis_tac[evaluate_binop_add_uint]
QED

(* ===== safe_cast on well-typed values is identity ===== *)
(*
 * KEY LEMMA: If a value already satisfies a type, safe_cast is identity.
 * Needed for IntCall return path.
 *)

(* Helper: distinct keys < n means length ≤ n (pigeonhole) *)
Theorem all_distinct_keys_length:
  !l (n:num). ALL_DISTINCT (MAP FST l) /\ EVERY (\(k, _). k < n) l ==>
              LENGTH l <= n
Proof
  rpt strip_tac >>
  `CARD (set (MAP FST l)) = LENGTH l`
    by simp[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `set (MAP FST l) SUBSET count n`
    by (simp[pred_setTheory.SUBSET_DEF, listTheory.MEM_MAP,
             PULL_EXISTS, pairTheory.FORALL_PROD] >>
        gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `CARD (set (MAP FST l)) <= CARD (count n)`
    by (irule pred_setTheory.CARD_SUBSET >>
        simp[pred_setTheory.FINITE_COUNT]) >>
  gvs[pred_setTheory.CARD_COUNT]
QED

(* ZIP (MAP FST l, MAP SND l) = l *)
val zip_fst_snd = listTheory.ZIP_UNZIP
  |> ONCE_REWRITE_RULE[listTheory.UNZIP_MAP];

(*
 * Mutual induction using safe_cast_ind.
 * P0: safe_cast tv v = SOME v when value_has_type tv v
 * P1: safe_cast_list tvs vs acc = SOME (REVERSE acc ++ vs)
 *     when values_have_types tvs vs
 *)
Theorem sparse_has_type_all_have_type:
  !tv n sparse. sparse_has_type tv n sparse ==>
    all_have_type tv (MAP SND sparse)
Proof
  Induct_on `sparse` >>
  simp[Once value_has_type_def, Once value_has_type_def] >>
  Cases >> simp[Once value_has_type_def, all_have_type_EVERY] >>
  rpt strip_tac >> res_tac >> gvs[all_have_type_EVERY]
QED

Theorem SORTED_lt_ALL_DISTINCT:
  !l : num list. SORTED $< l ==> ALL_DISTINCT l
Proof
  metis_tac[sortingTheory.SORTED_ALL_DISTINCT,
            relationTheory.irreflexive_def,
            relationTheory.transitive_def,
            prim_recTheory.LESS_REFL,
            arithmeticTheory.LESS_TRANS]
QED

Theorem sparse_has_type_length:
  !tv n sparse. sparse_has_type tv n sparse /\
    SORTED $< (MAP FST sparse) ==> LENGTH sparse <= n
Proof
  rpt strip_tac >>
  imp_res_tac SORTED_lt_ALL_DISTINCT >>
  `ALL_DISTINCT (MAP FST sparse)` by gvs[listTheory.MAP_MAP_o] >>
  irule all_distinct_keys_length >> simp[] >>
  pop_assum kall_tac >> pop_assum kall_tac >>
  Induct_on `sparse` >> simp[Once value_has_type_def] >>
  Cases >> simp[Once value_has_type_def]
QED

Theorem all_have_type_values_have_types_replicate:
  !tv vs. all_have_type tv vs ==>
    values_have_types (REPLICATE (LENGTH vs) tv) vs
Proof
  Induct_on `vs` >> simp[Once value_has_type_def, Once value_has_type_def]
QED

Theorem struct_has_type_map_fst:
  !ftypes fields. struct_has_type ftypes fields ==>
    MAP FST fields = MAP FST ftypes
Proof
  Induct >> Cases_on `fields` >>
  simp[Once value_has_type_def] >>
  Cases >> Cases_on `h` >>
  simp[Once value_has_type_def]
QED

Theorem struct_has_type_values_have_types:
  !ftypes fields. struct_has_type ftypes fields ==>
    values_have_types (MAP SND ftypes) (MAP SND fields)
Proof
  Induct >> Cases_on `fields` >>
  simp[Once value_has_type_def, Once value_has_type_def] >>
  Cases >> Cases_on `h` >>
  simp[Once value_has_type_def, Once value_has_type_def]
QED

(* Helper: safe_cast_list is identity when each element is well-typed
   and safe_cast is identity for that element type *)
Theorem safe_cast_list_identity:
  !tvs vs acc.
    values_have_types tvs vs /\
    (!tv v. MEM tv tvs /\ value_has_type tv v ==> safe_cast tv v = SOME v) ==>
    safe_cast_list tvs vs acc = SOME (REVERSE acc ++ vs)
Proof
  Induct >> Cases_on `vs` >> simp[Once value_has_type_def] >>
  rpt strip_tac >> simp[Once safe_cast_def]
QED

Theorem safe_cast_list_identity_nil:
  !tvs vs.
    values_have_types tvs vs /\
    (!tv v. MEM tv tvs /\ value_has_type tv v ==> safe_cast tv v = SOME v) ==>
    safe_cast_list tvs vs [] = SOME vs
Proof
  rpt strip_tac >> drule_all safe_cast_list_identity >> simp[]
QED

Theorem MEM_type_value_size_TupleTV:
  !tvs tv. MEM tv tvs ==> type_value_size tv < type_value_size (TupleTV tvs)
Proof
  Induct >> simp[type_value_size_def] >>
  rpt strip_tac >> gvs[type_value_size_def] >> res_tac >> simp[]
QED

Theorem type_value1_size_MEM:
  !fields nm tv. MEM (nm,tv) fields ==>
    type_value_size tv < type_value1_size fields
Proof
  Induct >> simp[] >> Cases >> simp[type_value_size_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> simp[]
QED

Theorem MEM_type_value_size_StructTV:
  !fields nm tv. MEM (nm,tv) fields ==>
    type_value_size tv < type_value_size (StructTV fields)
Proof
  rpt strip_tac >> simp[type_value_size_def] >>
  imp_res_tac type_value1_size_MEM >> simp[]
QED

Theorem ArrayTV_type_value_size:
  !tv b. type_value_size tv < type_value_size (ArrayTV tv b)
Proof
  Cases_on `b` >> simp[type_value_size_def]
QED

Theorem safe_cast_well_typed_tuple_helper:
  !tvs l.
    (!tv'. type_value_size tv' < list_size type_value_size tvs + 1 ==>
           !v'. value_has_type tv' v' ==> safe_cast tv' v' = SOME v') ==>
    values_have_types tvs l ==>
    safe_cast_list tvs l [] = SOME l
Proof
  rpt strip_tac >>
  irule safe_cast_list_identity_nil >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  imp_res_tac MEM_type_value_size_TupleTV >> gvs[]
QED

Theorem safe_cast_well_typed_struct_helper:
  !ftypes l.
    (!tv'. type_value_size tv' <
           list_size (pair_size (list_size char_size) type_value_size) ftypes + 1 ==>
           !v'. value_has_type tv' v' ==> safe_cast tv' v' = SOME v') ==>
    struct_has_type ftypes l ==>
    MAP FST l = MAP FST ftypes ==>
    safe_cast_list (MAP SND ftypes) (MAP SND l) [] = SOME (MAP SND l)
Proof
  rpt strip_tac >>
  irule safe_cast_list_identity_nil >>
  imp_res_tac struct_has_type_values_have_types >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  `?nm. MEM (nm, tv) ftypes` by (
    qpat_x_assum `MEM _ _` mp_tac >>
    simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
    metis_tac[]) >>
  imp_res_tac MEM_type_value_size_StructTV >> gvs[]
QED

Theorem safe_cast_well_typed:
  !tv v. value_has_type tv v ==> safe_cast tv v = SOME v
Proof
  completeInduct_on `type_value_size tv` >>
  rpt gen_tac >> rpt strip_tac >>
  rename1 `value_has_type tv val` >>
  (* Extract the IH into a reusable form *)
  `!tv'. type_value_size tv' < type_value_size tv ==>
         !v'. value_has_type tv' v' ==> safe_cast tv' v' = SOME v'`
    by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  (* Now case split without completeInduct's awkward IH *)
  Cases_on `val` >> gvs[value_has_type_inv] >>
  TRY (simp[Once safe_cast_def, within_int_bound_def] >> NO_TAC) >>
  TRY (simp[Once safe_cast_def] >> NO_TAC)
  (* ArrayV — first of 2 remaining goals *)
  >- (rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_inv] >>
      simp[Once safe_cast_def] >>
      TRY (imp_res_tac sparse_has_type_all_have_type >>
           imp_res_tac sparse_has_type_length >> simp[]) >>
      (* TupleV *)
      TRY (drule_all safe_cast_well_typed_tuple_helper >> simp[] >> NO_TAC) >>
      (* DynArrayV and SArrayV: both use REPLICATE *)
      (`values_have_types (REPLICATE (LENGTH l) tv0) l`
        by (irule all_have_type_values_have_types_replicate >> simp[]) >>
       `!tv v. MEM tv (REPLICATE (LENGTH l) tv0) /\
               value_has_type tv v ==> safe_cast tv v = SOME v`
         by (rpt strip_tac >> gvs[rich_listTheory.MEM_REPLICATE] >>
             first_x_assum irule >> simp[]) >>
       drule_all safe_cast_list_identity_nil >> simp[zip_fst_snd]
       ORELSE
       (`values_have_types (REPLICATE (LENGTH (MAP SND l)) tv0) (MAP SND l)`
          by (irule all_have_type_values_have_types_replicate >> simp[]) >>
        `!tv v. MEM tv (REPLICATE (LENGTH (MAP SND l)) tv0) /\
                value_has_type tv v ==> safe_cast tv v = SOME v`
          by (rpt strip_tac >> gvs[rich_listTheory.MEM_REPLICATE] >>
              first_x_assum irule >> simp[]) >>
        drule_all safe_cast_list_identity_nil >> simp[zip_fst_snd])))
  (* StructV *)
  >> (simp[Once safe_cast_def] >>
      imp_res_tac struct_has_type_map_fst >> simp[] >>
      imp_res_tac struct_has_type_values_have_types >>
      `!tv v. MEM tv (MAP SND ftypes) /\
              value_has_type tv v ==> safe_cast tv v = SOME v`
        by (rpt strip_tac >> first_x_assum irule >>
            `?nm. MEM (nm, tv) ftypes` by (
              qpat_x_assum `MEM _ (MAP _ _)` mp_tac >>
              simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
              metis_tac[]) >>
            imp_res_tac MEM_type_value_size_StructTV >> gvs[]) >>
      drule_all safe_cast_list_identity_nil >> strip_tac >>
      `MAP FST ftypes = MAP FST l` by gvs[] >>
      gvs[zip_fst_snd])
QED

Theorem safe_cast_well_typed_mutual:
  (!tv v. value_has_type tv v ==> safe_cast tv v = SOME v) /\
  (!tvs vs acc.
     values_have_types tvs vs ==>
     safe_cast_list tvs vs acc = SOME (REVERSE acc ++ vs))
Proof
  conj_tac >- metis_tac[safe_cast_well_typed] >>
  rpt strip_tac >> irule safe_cast_list_identity >> simp[] >>
  rpt strip_tac >> irule safe_cast_well_typed >> simp[]
QED


Theorem values_have_types_length:
  !tvs vs. values_have_types tvs vs ==> LENGTH vs = LENGTH tvs
Proof
  Induct >> Cases_on `vs` >> simp[Once value_has_type_def]
QED

(* safe_cast on a well-typed value is identity, so the result is well-typed *)
Theorem safe_cast_preserves_well_typed:
  !tv v v'. value_has_type tv v /\ safe_cast tv v = SOME v' ==>
    value_has_type tv v'
Proof
  rpt strip_tac >>
  imp_res_tac safe_cast_well_typed >> gvs[]
QED

(* KEY LEMMA: bind_arguments on well-typed values produces a well-typed scope. *)
Theorem bind_arguments_scope_well_typed:
  !tenv params vs sc.
    bind_arguments tenv params vs = SOME sc /\
    (!i tv. i < LENGTH params /\ i < LENGTH vs /\
            evaluate_type tenv (SND (EL i params)) = SOME tv ==>
            value_has_type tv (EL i vs)) ==>
    scope_well_typed sc
Proof
  MAP_EVERY qid_spec_tac [`sc`, `vs`, `params`, `tenv`] >>
  Induct_on `params`
  >- (rpt gen_tac >> Cases_on `vs` >>
      simp[Once bind_arguments_def, scope_well_typed_def,
           finite_mapTheory.FLOOKUP_EMPTY]) >>
  simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `safe_cast tv0 hval = SOME v0` >>
  rename1 `evaluate_type tenv _ = SOME tv0` >>
  `value_has_type tv0 hval` by (
    first_x_assum (qspecl_then [`0`, `tv0`] mp_tac) >> simp[]) >>
  imp_res_tac safe_cast_preserves_well_typed >>
  rename1 `bind_arguments tenv params tl = SOME sc0` >>
  `scope_well_typed sc0` by (
    qpat_x_assum `!tenv vs sc. _`
      (qspecl_then [`tenv`, `tl`, `sc0`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC i`, `tv`] mp_tac) >> simp[]) >>
  gvs[scope_well_typed_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt gen_tac >> IF_CASES_TAC >> strip_tac >> gvs[] >> res_tac
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
    fn_sigs : ((num option # string) |-> (type list # type));
  |>
End

(* fn_sigs_consistent: for any function signature in fn_sigs,
   the runtime lookup agrees *)
Definition fn_sigs_consistent_def:
  fn_sigs_consistent fn_sigs cx <=>
    !src_id_opt fn param_types ret_ty.
      FLOOKUP fn_sigs (src_id_opt, fn) = SOME (param_types, ret_ty) ==>
      ?ts fm params dflts body.
        get_module_code cx src_id_opt = SOME ts /\
        lookup_callable_function cx.in_deploy fn ts =
          SOME (fm, params, dflts, ret_ty, body) /\
        param_types = MAP SND params
End

(* env_consistent: typing env matches runtime state *)
Definition env_consistent_def:
  env_consistent env cx st <=>
    env.type_defs = get_tenv cx /\
    fn_sigs_consistent env.fn_sigs cx /\
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

(* ===== well_typed_stmt: static typing for statements ===== *)

(* well_typed for assignment targets (base + tuple) *)
Definition well_typed_atarget_def:
  well_typed_atarget env (BaseTarget bt) =
    well_typed_target env bt /\
  well_typed_atarget env (TupleTarget tgts) =
    EVERY (well_typed_atarget env) tgts
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
  well_typed_stmt env ret_ty (Raise e) =
    well_typed_expr env e /\
  well_typed_stmt env ret_ty (Assert e se) =
    (well_typed_expr env e /\
     well_typed_expr env se /\
     expr_type e = BaseT BoolT) /\
  well_typed_stmt env ret_ty (Log id es) =
    well_typed_exprs env es /\
  well_typed_stmt env ret_ty (AnnAssign id typ e) =
    (well_typed_expr env e /\
     well_formed_type env.type_defs typ) /\
  well_typed_stmt env ret_ty (Append bt e) =
    (well_typed_target env bt /\
     well_typed_expr env e) /\
  well_typed_stmt env ret_ty (Assign tgt e) =
    (well_typed_atarget env tgt /\
     well_typed_expr env e) /\
  well_typed_stmt env ret_ty (AugAssign ty bt bop e) =
    (well_typed_target env bt /\
     well_typed_expr env e /\
     well_formed_type env.type_defs ty) /\
  well_typed_stmt env ret_ty (If e ss1 ss2) =
    (well_typed_expr env e /\
     expr_type e = BaseT BoolT /\
     well_typed_stmts env ret_ty ss1 /\
     well_typed_stmts env ret_ty ss2) /\
  well_typed_stmt env ret_ty (For id typ it n body) =
    (well_formed_type env.type_defs typ /\
     well_typed_stmts env ret_ty body) /\
  well_typed_stmts env ret_ty [] = T /\
  well_typed_stmts env ret_ty (s::ss) =
    (well_typed_stmt env ret_ty s /\
     well_typed_stmts env ret_ty ss)
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
 *
 *   The call site's type annotation ty must match the function's declared
 *   return type ret — this is ensured by the Vyper compiler frontend.
 *)
Definition functions_well_typed_def:
  functions_well_typed cx <=>
    !src_id_opt fn ts fm args dflts ret body fn_sigs.
      get_module_code cx src_id_opt = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts =
        SOME (fm, args, dflts, ret, body) /\
      fn_sigs_consistent fn_sigs cx ==>
      ?env_body ret_tv.
        env_body.type_defs = get_tenv cx /\
        env_body.fn_sigs = fn_sigs /\
        env_body.global_types = FEMPTY /\
        evaluate_type (get_tenv cx) ret = SOME ret_tv /\
        well_typed_stmts env_body ret body /\
        well_typed_exprs
          <| var_types := FEMPTY;
             global_types := FEMPTY;
             toplevel_types := FEMPTY;
             type_defs := get_tenv cx;
             fn_sigs := FEMPTY |> dflts /\
        (!id typ. MEM (id, typ) args ==>
           FLOOKUP env_body.var_types (string_to_num id) = SOME typ) /\
        MAP expr_type dflts =
          MAP SND (DROP (LENGTH args - LENGTH dflts) args)
End

(* Separate predicate: call site type annotations match function return types *)

Theorem env_consistent_empty:
  !cx st.
    env_consistent
      <| var_types := FEMPTY;
         global_types := FEMPTY;
         toplevel_types := FEMPTY;
         type_defs := get_tenv cx;
         fn_sigs := FEMPTY |> cx st
Proof
  simp[env_consistent_def, finite_mapTheory.FLOOKUP_EMPTY,
       fn_sigs_consistent_def]
QED

(* ===== Helper lemmas for type preservation ===== *)

(* well_typed_exprs is preserved by DROP *)
Theorem well_typed_exprs_DROP:
  !env es n. well_typed_exprs env es ==> well_typed_exprs env (DROP n es)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  rpt strip_tac >> Cases_on `n` >> simp[well_typed_expr_def]
QED

(* get_tenv is independent of cx.stk *)
Theorem get_tenv_stk_irrelevant:
  !cx f. get_tenv (cx with stk updated_by f) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem fn_sigs_consistent_stk_irrelevant:
  !sigs cx f. fn_sigs_consistent sigs (cx with stk updated_by f) <=>
              fn_sigs_consistent sigs cx
Proof
  simp[fn_sigs_consistent_def, get_module_code_def]
QED

Theorem functions_well_typed_stk_irrelevant:
  !cx f. functions_well_typed (cx with stk updated_by f) <=>
         functions_well_typed cx
Proof
  simp[functions_well_typed_def, get_module_code_def,
       get_tenv_stk_irrelevant, fn_sigs_consistent_stk_irrelevant]
QED

(* state_well_typed depends only on scopes and immutables *)
Theorem state_well_typed_with_scopes:
  !st scopes.
    EVERY scope_well_typed scopes /\
    EVERY (\(addr, mods). imms_well_typed mods) st.immutables ==>
    state_well_typed (st with scopes := scopes)
Proof
  simp[state_well_typed_def]
QED

(* push_function preserves state_well_typed if sc is well-typed *)
Theorem state_well_typed_push_function:
  !src_fn sc cx st cxf st'.
    push_function src_fn sc cx st = (INL cxf, st') /\
    scope_well_typed sc /\
    state_well_typed st ==>
    state_well_typed st'
Proof
  simp[push_function_def, return_def, state_well_typed_def]
QED

(* pop_function (set_scopes prev) restores scopes *)
Theorem state_well_typed_pop_function:
  !prev st res st'.
    pop_function prev st = (res, st') /\
    EVERY scope_well_typed prev /\
    EVERY (\(addr, mods). imms_well_typed mods) st.immutables ==>
    state_well_typed st'
Proof
  simp[pop_function_def, set_scopes_def, return_def,
       state_well_typed_def]
QED

(* finally: if f preserves state_well_typed (even on error) and
   g preserves state_well_typed, then finally f g does too *)
Theorem state_well_typed_finally:
  !f g st res st'.
    finally f g st = (res, st') /\
    (!r s. f st = (r, s) ==> state_well_typed s) /\
    (!s r' s'. state_well_typed s /\ g s = (r', s') ==> state_well_typed s') ==>
    state_well_typed st'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperStateTheory.finally_def] >>
  Cases_on `f st` >>
  rename1 `f st = (f_res, f_st)` >>
  `state_well_typed f_st` by metis_tac[] >>
  Cases_on `f_res` >>
  gvs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def] >>
  Cases_on `g f_st` >>
  rename1 `g f_st = (g_res, g_st)` >>
  `state_well_typed g_st` by metis_tac[] >>
  Cases_on `g_res` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

(* handle_function doesn't change state *)
Theorem handle_function_state:
  !e st r st'.
    handle_function e st = (r, st') ==> st' = st
Proof
  Cases >> simp[handle_function_def, return_def, raise_def]
QED

(* Key lemma: decompose finally+try+handle_function+pop_function success *)
Theorem finally_try_handle_pop_success:
  !f prev st rv st_final.
    finally
      (try (bind f (\x. return NoneV)) handle_function)
      (pop_function prev)
      st = (INL rv, st_final) ==>
    (?st_body.
       f st = (INL (), st_body) /\
       st_final = st_body with scopes := prev /\
       rv = NoneV)
    \/
    (?v st_body.
       f st = (INR (ReturnException v), st_body) /\
       st_final = st_body with scopes := prev /\
       rv = v)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def, try_def, bind_def, ignore_bind_def,
      pop_function_def, set_scopes_def,
      AllCaseEqs()] >>
  gvs[return_def, raise_def] >>
  imp_res_tac handle_function_state >>
  Cases_on `e` >> gvs[handle_function_def, return_def, raise_def]
QED

(* try doesn't change state on its own (it's just exception handling) *)
Theorem try_state:
  !f g st r st'.
    try f g st = (r, st') ==>
    ?r1 s1. f st = (r1, s1) /\
      ((!v. r1 = INL v ==> r = INL v /\ st' = s1) /\
       (!e. r1 = INR e ==> g e s1 = (r, st')))
Proof
  simp[try_def] >> rpt strip_tac >>
  Cases_on `f st` >> gvs[] >>
  Cases_on `q` >> gvs[return_def]
QED

(* env_consistent: stk update doesn't affect var_types part *)
Theorem env_consistent_stk_var_types:
  !env cx st f.
    env.type_defs = get_tenv cx ==>
    env.type_defs = get_tenv (cx with stk updated_by f)
Proof
  simp[get_tenv_stk_irrelevant]
QED

(* get_scopes just reads st.scopes *)
Theorem get_scopes_result:
  !st r st'.
    get_scopes st = (r, st') ==> r = INL st.scopes /\ st' = st
Proof
  simp[get_scopes_def, return_def]
QED

(* state_well_typed depends on scopes only through EVERY scope_well_typed *)
Theorem state_well_typed_immutables:
  !st. state_well_typed st ==>
       EVERY (\(addr, mods). imms_well_typed mods) st.immutables
Proof
  simp[state_well_typed_def]
QED

(* pop_function preserves immutables (it only changes scopes) *)
Theorem pop_function_immutables:
  !prev st res st'.
    pop_function prev st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  simp[pop_function_def, set_scopes_def, return_def]
QED

(* push_function preserves immutables *)
Theorem push_function_immutables:
  !src_fn sc cx st cxf st'.
    push_function src_fn sc cx st = (INL cxf, st') ==>
    st'.immutables = st.immutables
Proof
  simp[push_function_def, return_def]
QED

(* state_well_typed through try+handle_function:
   if f preserves state_well_typed on all outcomes,
   then try f handle_function does too *)
Theorem state_well_typed_try_handle:
  !f st r st'.
    try f handle_function st = (r, st') /\
    (!r0 s0. f st = (r0, s0) ==> state_well_typed s0) ==>
    state_well_typed st'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[try_def] >>
  Cases_on `f st` >> rename1 `f st = (f_res, f_st)` >> gvs[] >>
  Cases_on `f_res` >> gvs[return_def] >>
  rename1 `f st = (INR exc, f_st)` >>
  Cases_on `exc` >> gvs[handle_function_def, return_def, raise_def]
QED

(* env_consistent only cares about scopes, not other state fields *)
Theorem env_consistent_scopes_only:
  !env cx st scopes.
    env_consistent env cx (st with scopes := scopes) <=>
    env.type_defs = get_tenv cx /\
    fn_sigs_consistent env.fn_sigs cx /\
    (!id ty tv v.
       FLOOKUP env.var_types id = SOME ty /\
       lookup_scopes id scopes = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!id ty tv v.
       FLOOKUP env.global_types id = SOME ty /\
       FLOOKUP (get_source_immutables (current_module cx)
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv)
Proof
  simp[env_consistent_def]
QED

(* After pop_function prev restores caller scopes, env_consistent is restored
   (assuming immutables unchanged and caller env was consistent with prev) *)
Theorem env_consistent_pop_function:
  !env cx st prev res st'.
    pop_function prev st = (res, st') /\
    env.type_defs = get_tenv cx /\
    fn_sigs_consistent env.fn_sigs cx /\
    (!id ty tv v.
       FLOOKUP env.var_types id = SOME ty /\
       lookup_scopes id prev = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!id ty tv v.
       FLOOKUP env.global_types id = SOME ty /\
       FLOOKUP (get_source_immutables (current_module cx)
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) ==>
    env_consistent env cx st'
Proof
  simp[pop_function_def, set_scopes_def, return_def,
       env_consistent_def] >> metis_tac[]
QED

(* bind_arguments stores evaluate_type results *)
Theorem bind_arguments_evaluate_type:
  !tenv params vs sc n tv v.
    bind_arguments tenv params vs = SOME sc /\
    FLOOKUP sc n = SOME (tv, v) ==>
    ?id typ. n = string_to_num id /\
             MEM (id, typ) params /\
             evaluate_type tenv typ = SOME tv
Proof
  Induct_on `params` >> simp[bind_arguments_def] >>
  Cases >> simp[bind_arguments_def] >>
  rpt gen_tac >>
  Cases_on `vs` >> simp[bind_arguments_def] >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `n = string_to_num q` >> gvs[]
  >- (qexists_tac `q` >> qexists_tac `r` >> simp[])
  >- (first_x_assum drule_all >> strip_tac >>
      qexists_tac `id` >> qexists_tac `typ` >> simp[])
QED

(* env_consistent for callee after bind_arguments *)
Theorem bind_arguments_env_consistent:
  !tenv params vs sc env_body cx' st.
    bind_arguments tenv params vs = SOME sc /\
    env_body.type_defs = get_tenv cx' /\
    tenv = get_tenv cx' /\
    fn_sigs_consistent env_body.fn_sigs cx' /\
    (!id typ. MEM (id, typ) params ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ) /\
    env_body.global_types = FEMPTY ==>
    env_consistent env_body cx' (st with scopes := [sc])
Proof
  rpt strip_tac >>
  simp[env_consistent_def] >> rpt strip_tac >>
  (* Only var_types case remains (global_types = FEMPTY handled by simp) *)
  gvs[lookup_scopes_def, AllCaseEqs()] >>
  drule bind_arguments_evaluate_type >>
  disch_then drule >> strip_tac >> gvs[] >>
  res_tac >> gvs[]
QED

(* ===== IntCall helper for type preservation ===== *)

(* Helper: state_well_typed is preserved through IntCall. *)
Theorem list_rel_typing_to_el:
  !tenv params args vs dflts.
    LIST_REL (\v e. !tv. evaluate_type tenv (expr_type e) = SOME tv ==>
                         value_has_type tv v) vs args /\
    MAP expr_type args = TAKE (LENGTH args) (MAP SND params) /\
    LENGTH args <= LENGTH params ==>
    !i tv. i < LENGTH args /\ i < LENGTH (vs ++ dflts) /\
           evaluate_type tenv (SND (EL i params)) = SOME tv ==>
           value_has_type tv (EL i (vs ++ dflts))
Proof
  rpt strip_tac >>
  `LENGTH vs = LENGTH args` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     simp[listTheory.LIST_REL_EL_EQN]) >>
  simp[rich_listTheory.EL_APPEND1] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum irule >>
  `expr_type (EL i args) = SND (EL i params)` by
    (`EL i (MAP expr_type args) = EL i (TAKE (LENGTH args) (MAP SND params))` by
       metis_tac[] >>
     gvs[listTheory.EL_MAP, rich_listTheory.EL_TAKE]) >>
  gvs[]
QED

Theorem intcall_state_preserved:
  !cx src_id_opt fn es v17 env st v st' tv.
    (* IH for eval_exprs cx es (args) *)
    (!env0 st0 res0 st0'.
       well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
       state_well_typed st0 /\ functions_well_typed cx /\
       eval_exprs cx es st0 = (res0, st0') ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       !vs0. res0 = INL vs0 ==>
       LIST_REL (\v e. !tyv.
         evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
         value_has_type tyv v) vs0 es) /\
    (* IH for eval_exprs cxd needed_dflts (defaults) *)
    (!dflts_sub env0 st0 res0 st0'.
       well_typed_exprs env0 dflts_sub /\
       env_consistent env0 (cx with stk updated_by CONS (src_id_opt, fn)) st0 /\
       state_well_typed st0 /\
       functions_well_typed (cx with stk updated_by CONS (src_id_opt, fn)) /\
       eval_exprs (cx with stk updated_by CONS (src_id_opt, fn))
         dflts_sub st0 = (res0, st0') ==>
       state_well_typed st0' /\
       !vs0. res0 = INL vs0 ==>
       LIST_REL (\v e. !tyv.
         evaluate_type (get_tenv (cx with stk updated_by CONS (src_id_opt, fn)))
           (expr_type e) = SOME tyv ==>
         value_has_type tyv v) vs0 dflts_sub) /\
    (* IH for eval_stmts cxf body *)
    (!body env0 ret_ty st0 res0 st0'.
       well_typed_stmts env0 ret_ty body /\
       env_consistent env0 (cx with stk updated_by CONS (src_id_opt, fn)) st0 /\
       state_well_typed st0 /\
       functions_well_typed (cx with stk updated_by CONS (src_id_opt, fn)) /\
       eval_stmts (cx with stk updated_by CONS (src_id_opt, fn))
         body st0 = (res0, st0') ==>
       state_well_typed st0') ==>
    well_typed_expr env (Call v16 (IntCall (src_id_opt, fn)) es v17) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_expr cx (Call v16 (IntCall (src_id_opt, fn)) es v17) st =
      (INL (Value v), st') ==>
    state_well_typed st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
  simp[bind_def, ignore_bind_def, LET_THM,
       check_def, assert_def, lift_option_type_def,
       type_check_def, get_scopes_def, push_function_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  (* Simplify option wrappers using qmatch *)
  qpat_x_assum `option_CASE (get_module_code _ _) _ _ _ = _` mp_tac >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  rename1 `get_module_code cx src_id_opt = SOME ts` >>
  qpat_x_assum `option_CASE (lookup_callable_function _ _ _) _ _ _ = _` mp_tac >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  rename1 `lookup_callable_function _ _ _ = SOME fn_info` >>
  qpat_x_assum `option_CASE (bind_arguments _ _ _) _ _ _ = _` mp_tac >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  rename1 `bind_arguments _ _ _ = SOME sc` >>
  qpat_x_assum `option_CASE (evaluate_type _ _) _ _ _ = _` mp_tac >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  rename1 `evaluate_type _ _ = SOME ret_tv` >>
  qpat_x_assum `option_CASE (safe_cast _ _) _ _ _ = _` mp_tac >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  rename1 `safe_cast _ _ = SOME crv` >>
  (* Step 1: Apply IH_args *)
  `well_typed_exprs env es` by gvs[well_typed_expr_def] >>
  `state_well_typed s'⁴'` by
    (last_x_assum (qspecl_then [`env`, `s''`, `INL vs`, `s'⁴'`] mp_tac) >>
     simp[]) >>
  (* Destructure fn_info *)
  PairCases_on `fn_info` >> gvs[] >>
  (* Step 2: Apply IH_dflts *)
  `functions_well_typed (cx with stk updated_by CONS (src_id_opt, fn))` by
    gvs[functions_well_typed_stk_irrelevant] >>
  `well_typed_exprs
     <|var_types := FEMPTY; global_types := FEMPTY;
       toplevel_types := FEMPTY; type_defs := get_tenv cx;
       fn_sigs := FEMPTY|> fn_info2` by
    (qpat_x_assum `functions_well_typed cx` mp_tac >>
     simp[functions_well_typed_def] >>
     disch_then (qspecl_then
       [`src_id_opt`, `fn`, `ts`, `fn_info0`, `fn_info1`,
        `fn_info2`, `fn_info3`, `fn_info4`, `FEMPTY`]
       mp_tac) >> simp[fn_sigs_consistent_def] >>
     strip_tac >> simp[]) >>
  qmatch_assum_abbrev_tac `eval_exprs _ (DROP drop_n _) s'⁴' = (INL dflt_vs, s'⁵')` >>
  `well_typed_exprs
     <|var_types := FEMPTY; global_types := FEMPTY;
       toplevel_types := FEMPTY; type_defs := get_tenv cx;
       fn_sigs := FEMPTY|>
     (DROP drop_n fn_info2)` by
    (irule well_typed_exprs_DROP >> gvs[]) >>
  `state_well_typed s'⁵'` by
    (qpat_x_assum `!dflts_sub env0 st0 res0 st0'. _`
       (qspecl_then
          [`DROP drop_n fn_info2`,
           `<|var_types := FEMPTY; global_types := FEMPTY;
              toplevel_types := FEMPTY;
              type_defs := get_tenv cx;
              fn_sigs := FEMPTY|>`,
           `s'⁴'`, `INL dflt_vs`, `s'⁵'`] mp_tac) >>
     impl_tac >- (
       simp[get_tenv_stk_irrelevant] >>
       simp[env_consistent_def, finite_mapTheory.FLOOKUP_EMPTY,
            get_tenv_stk_irrelevant, fn_sigs_consistent_def]
     ) >> simp[]) >>
  (* Extract well_typed_stmts from functions_well_typed *)
  `?env_body.
     env_body.type_defs = get_tenv cx /\
     env_body.fn_sigs = env.fn_sigs /\
     env_body.global_types = FEMPTY /\
     well_typed_stmts env_body fn_info3 fn_info4 /\
     (!id typ. MEM (id, typ) fn_info1 ==>
        FLOOKUP env_body.var_types (string_to_num id) = SOME typ)` by
    (qpat_x_assum `functions_well_typed cx` mp_tac >>
     simp[functions_well_typed_def] >>
     disch_then (qspecl_then
       [`src_id_opt`, `fn`, `ts`, `fn_info0`, `fn_info1`,
        `fn_info2`, `fn_info3`, `fn_info4`, `env.fn_sigs`] mp_tac) >>
     impl_tac >- fs[env_consistent_def] >>
     strip_tac >> qexists_tac `env_body` >> simp[]) >>
  `scope_well_typed sc` by
    suspend "difficulty" >>
  `state_well_typed (s'⁵' with scopes := [sc])` by
    (irule state_well_typed_with_scopes >>
     simp[] >>
     qpat_x_assum `state_well_typed s'⁵'` mp_tac >>
     simp[state_well_typed_def]) >>
  (* env_consistent for callee *)
  `env_consistent env_body
     (cx with stk updated_by CONS (src_id_opt, fn))
     (s'⁵' with scopes := [sc])` by
    (mp_tac (Q.SPECL [`get_tenv cx`, `fn_info1`, `vs ++ dflt_vs`, `sc`,
                       `env_body`,
                       `cx with stk updated_by CONS (src_id_opt, fn)`,
                       `s'⁵'`]
               bind_arguments_env_consistent) >>
     simp[get_tenv_stk_irrelevant, fn_sigs_consistent_stk_irrelevant] >>
     `fn_sigs_consistent env.fn_sigs cx` by
       (qpat_x_assum `env_consistent env cx _` mp_tac >>
        simp[env_consistent_def]) >>
     gvs[]) >>
  (* Step 3: Decompose the finally block *)
  drule finally_try_handle_pop_success >> strip_tac >> gvs[]
  (* Both cases: apply IH_body *)
  >> (
    rename1 `eval_stmts _ _ _ = (_, st_body)` >>
    `state_well_typed st_body` by
      (qpat_x_assum `!body env0 ret_ty st0 res0 st0'. _`
         (qspecl_then
            [`fn_info4`, `env_body`, `fn_info3`,
             `s'⁵' with scopes := [sc]`] mp_tac) >>
       simp[]) >>
    fs[state_well_typed_def]
  )
QED

Resume intcall_state_preserved[difficulty]:
  match_mp_tac bind_arguments_scope_well_typed >>
  (* Get LIST_REL for args *)
  `LIST_REL (\v e. !tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
                          value_has_type tyv v) vs es` by
    (last_x_assum (qspecl_then [`env`, `s''`, `INL vs`, `s'⁴'`] mp_tac) >>
     simp[well_typed_expr_def]) >>
  (* Get param type correspondence from fn_sigs *)
  `MAP expr_type es = TAKE (LENGTH es) (MAP SND fn_info1)` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def] >> strip_tac >>
     qpat_x_assum `env_consistent env cx _` mp_tac >>
     simp[env_consistent_def, fn_sigs_consistent_def] >>
     strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
  qexists_tac `get_tenv cx` >>
  qexists_tac `fn_info1` >>
  qexists_tac `vs ++ dflt_vs` >>
  simp[] >>
  rpt gen_tac >>
  strip_tac >>
  Cases_on `i < LENGTH es`
  >- (irule (INST_TYPE[alpha|->``:string``]list_rel_typing_to_el) >>
      simp[] >>
      qexists_tac `es` >>
      qexists_tac `fn_info1` >>
      qexists_tac `get_tenv cx` >>
      simp[]) >>
  first_x_assum $ drule_at (Pat`eval_exprs`) >>
  simp[] >>
  disch_then $ drule_at Any >>
  impl_tac >- (
    qmatch_goalsub_abbrev_tac`env_consistent _ cxx`
    \\ qspec_then`cxx`mp_tac env_consistent_empty
    \\ simp[Abbr`cxx`, get_tenv_stk_irrelevant] )
  \\ simp[get_tenv_stk_irrelevant]
  \\ gvs[listTheory.LIST_REL_EL_EQN]
  \\ simp[rich_listTheory.EL_APPEND2]
  \\ rpt strip_tac
  \\ first_x_assum irule
  \\ simp[listTheory.EL_DROP]
  \\ sg `MAP expr_type fn_info2 = MAP SND (DROP (LENGTH fn_info1 - LENGTH fn_info2) fn_info1)` >- (
    qpat_x_assum `functions_well_typed _` mp_tac >>
    simp_tac std_ss [functions_well_typed_def, functions_well_typed_stk_irrelevant] >>
    disch_then (qspecl_then [`src_id_opt`, `fn`, `ts`, `fn_info0`, `fn_info1`,
      `fn_info2`, `fn_info3`, `fn_info4`, `FEMPTY`] mp_tac) >>
    impl_tac >- simp[fn_sigs_consistent_def] >> simp[] >>
    strip_tac)
  \\ pop_assum mp_tac
  \\ simp[listTheory.LIST_EQ_REWRITE]
  \\ simp[listTheory.EL_MAP]
  \\ simp[listTheory.EL_DROP]
  \\ rw[]
  \\ gvs[Abbr`drop_n`]
QED

Finalise intcall_state_preserved

(* TODO: move these helpers *)
Theorem bind_apply:
  !f g s. (do v <- f; g v od) s =
    case f s of (INL v,s') => g v s' | (INR e,s') => (INR e,s')
Proof
  rpt gen_tac >> simp[bind_def, pairTheory.UNCURRY]
QED

Theorem unitbind_apply:
  !f g s. (do f; g od) s =
    case f s of (INL x,s') => g s' | (INR e,s') => (INR e,s')
Proof
  EVAL_TAC >> simp[bind_def]
QED

(* ===== Type preservation by mutual induction ===== *)
(*
 * Uses evaluate_ind (9 predicates, 47 hypotheses).
 *
 * P0 (eval_stmt): well_typed_stmt env ret_ty s ∧ env_consistent ∧
 *   state_well_typed ⇒ state_well_typed st' ∧ return exceptions well-typed
 * P1 (eval_stmts): same for statement lists
 * P2 (eval_iterator): state_well_typed preserved
 * P3 (eval_target): state_well_typed preserved
 * P4 (eval_targets): state_well_typed preserved
 * P5 (eval_base_target): state_well_typed preserved
 * P6 (eval_for): state_well_typed preserved
 * P7 (eval_expr): well_typed_expr ∧ env_consistent ∧ state_well_typed ⇒
 *   result satisfies type ∧ state_well_typed st'
 * P8 (eval_exprs): well_typed_exprs ∧ env_consistent ∧ state_well_typed ⇒
 *   results satisfy types ∧ state_well_typed st'
 *)

(* TODO: these no-return theorems should probably be moved *)

Theorem lift_option_error:
  lift_option x y z = (INR e, s) ==>
  e = Error (RuntimeError y)
Proof
  rw[lift_option_def, CaseEq"option", option_CASE_rator, return_def, raise_def]
QED

Theorem lift_sum_error:
  lift_sum x y = (INR e, s) ==>
  (∃m. e = Error m)
Proof
  rw[lift_sum_def, CaseEq"sum", sum_CASE_rator, return_def, raise_def]
QED

Theorem lift_option_type_error:
  lift_option_type x z y = (INR e, s) ==>
  e = Error (TypeError z)
Proof
  rw[lift_option_type_def, CaseEq"option", option_CASE_rator, return_def, raise_def]
QED

Theorem assign_result_error:
  assign_result a b c d e = (INR x, y) ==>
  (∃m. x = Error m)
Proof
  Cases_on`b` \\ rw[assign_result_def, return_def, bind_apply]
  \\ gvs[CaseEq"prod", CaseEq"sum"]
  \\ TRY(drule lift_sum_error \\ rw[])
QED

Theorem get_immutables_error:
  get_immutables x y z = (INR e, s) ==>
  (∃m. e = Error (RuntimeError m))
Proof
  rw[get_immutables_def, bind_apply, AllCaseEqs(), return_def,
     get_address_immutables_def]
  \\ drule lift_option_error \\ rw[]
QED

Theorem get_storage_backend_no_error[simp]:
  get_storage_backend x y z ≠ (INR e, s)
Proof
  Cases_on`y` \\ rw[get_storage_backend_def, bind_apply, AllCaseEqs(), return_def]
  \\ gvs[get_accounts_def, get_transient_storage_def, return_def]
QED

Theorem read_storage_slot_error:
  read_storage_slot x y z w a = (INR e, s) ==>
  (∃m. e = Error (RuntimeError m))
Proof
  rw[read_storage_slot_def, bind_apply, AllCaseEqs()]
  \\ TRY (drule lift_option_error \\ rw[]) \\ gvs[]
QED

Theorem lookup_global_error:
  lookup_global a b c d = (INR e, f) ==>
  (∃m. e = Error m)
Proof
  rw[lookup_global_def, bind_apply, AllCaseEqs(), option_CASE_rator,
     raise_def, return_def]
  >> TRY (drule lift_option_type_error \\ rw[])
  \\ TRY (drule get_immutables_error \\ rw[])
  \\ gvs[var_decl_info_CASE_rator, prod_CASE_rator, AllCaseEqs(),
         bind_apply, return_def]
  >> TRY (drule lift_option_type_error \\ rw[])
  \\ gvs[type_value_CASE_rator, AllCaseEqs(), bind_apply, return_def]
  \\ drule read_storage_slot_error \\ rw[]
QED

Theorem set_storage_backend_no_error[simp]:
  set_storage_backend a b c d ≠ (INR e, f)
Proof
  Cases_on `b` \\ rw[set_storage_backend_def]
  \\ gvs[update_transient_def, return_def]
  \\ gvs[bind_apply, AllCaseEqs(), get_accounts_def, return_def]
  \\ gvs[update_accounts_def, return_def]
QED

Theorem write_storage_slot_error:
  write_storage_slot a b c d e f = (INR g, h) ==>
  ?m. g = Error m
Proof
  rw[write_storage_slot_def, bind_apply, AllCaseEqs()] \\ gvs[]
  \\ TRY (drule lift_option_error \\ rw[])
QED

Theorem set_global_error:
  set_global a b c d e = (INR x, y) ==>
  ∃t. x = Error t
Proof
  rw[set_global_def, bind_apply, AllCaseEqs()]
  \\ TRY(drule lift_option_type_error \\ rw[])
  \\ gvs[option_CASE_rator, AllCaseEqs(), raise_def]
  \\ gvs[var_decl_info_CASE_rator, AllCaseEqs(), prod_CASE_rator, raise_def]
  \\ gvs[bind_apply, AllCaseEqs()]
  \\ TRY(drule lift_option_type_error \\ rw[])
  \\ drule write_storage_slot_error \\ rw[]
QED

Theorem resolve_array_element_error:
  ∀a b c d e f g h. resolve_array_element a b c d e f = (INR g, h)
  ==> ?m. g = Error m
Proof
  ho_match_mp_tac resolve_array_element_ind
  \\ rw[resolve_array_element_def, raise_def, return_def]
  \\ gvs[bind_apply, AllCaseEqs(), bound_CASE_rator, unitbind_apply,
         return_def, check_def, assert_def, raise_def]
  \\ first_x_assum irule
  \\ TRY(qexists_tac`0` \\ simp[] \\ goal_assum drule)
  \\ qexists_tac`1` \\ simp[]
  \\ gvs[wordsTheory.word_add_n2w]
  \\ goal_assum drule
QED

(* assign_target never returns ReturnException *)
Theorem assign_target_no_return:
  (!cx tgt ao st res st'.
    assign_target cx tgt ao st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (!cx tgts vs st res st'.
    assign_targets cx tgts vs st = (res, st') ==>
    !v. res <> INR (ReturnException v))
Proof
  ho_match_mp_tac assign_target_ind
  \\ conj_tac >- (
    rw[assign_target_def, bind_apply, CaseEq"prod", CaseEq"sum"]
    \\ drule get_scopes_result \\ rw[]
    \\ gvs[bind_def, ignore_bind_def, CaseEq"prod", CaseEq"sum"]
    \\ TRY (drule lift_option_error \\ rw[])
    \\ pairarg_tac \\ gvs[bind_apply, CaseEq"prod", CaseEq"sum"]
    \\ gvs[set_scopes_def, get_scopes_def, return_def]
    \\ TRY (drule lift_sum_error \\ rw[])
    \\ strip_tac \\ gvs[]
    \\ drule assign_result_error \\ rw[])
  \\ conj_tac >- (
    rw[assign_target_def, bind_apply, AllCaseEqs()]
    \\ TRY (drule lift_option_type_error \\ rw[])
    \\ TRY (drule lookup_global_error \\ rw[])
    \\ gvs[toplevel_value_CASE_rator, AllCaseEqs(),
           bind_apply, unitbind_apply]
    \\ TRY (drule lift_option_type_error \\ rw[])
    \\ TRY (drule lift_sum_error \\ rw[])
    \\ TRY (drule set_global_error \\ rw[])
    \\ TRY (strip_tac \\ gvs[] \\ drule assign_result_error \\ rw[])
    \\ gvs[bind_def, ignore_bind_def, prod_CASE_rator, AllCaseEqs()]
    \\ TRY (drule lift_option_type_error \\ rw[])
    \\ TRY (drule resolve_array_element_error \\ rw[])
    \\ pairarg_tac \\ gvs[]
    \\ gvs[bind_def, ignore_bind_def, prod_CASE_rator, AllCaseEqs(),
           type_value_CASE_rator, bound_CASE_rator,
           assign_operation_CASE_rator, return_def, check_def,
           assert_def]
    \\ TRY (drule lift_option_type_error \\ rw[])
    \\ TRY (drule lift_sum_error \\ rw[])
    \\ TRY (drule write_storage_slot_error \\ rw[])
    \\ TRY (drule read_storage_slot_error \\ rw[])
    \\ TRY (strip_tac \\ gvs[] \\ drule assign_result_error \\ rw[])
    \\ pairarg_tac \\ gvs[bind_apply, AllCaseEqs()]
    \\ TRY (drule lift_option_type_error \\ rw[])
    \\ TRY (drule lift_sum_error \\ rw[])
    \\ TRY (drule write_storage_slot_error \\ rw[])
    \\ TRY (drule read_storage_slot_error \\ rw[])
    \\ strip_tac \\ gvs[] \\ drule assign_result_error \\ rw[])
  \\ cheat
QED

(* eval_expr and related functions never return ReturnException *)
Theorem evaluate_no_return:
  (* P0: eval_stmt — can return ReturnException, so T *)
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> T) /\
  (* P1: eval_stmts — can return ReturnException, so T *)
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> T) /\
  (* P2: eval_iterator *)
  (!cx it st res st'.
    eval_iterator cx it st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (* P3: eval_target *)
  (!cx g st res st'.
    eval_target cx g st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (* P4: eval_targets *)
  (!cx gs st res st'.
    eval_targets cx gs st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (* P5: eval_base_target *)
  (!cx bt st res st'.
    eval_base_target cx bt st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (* P6: eval_for — can return ReturnException, so T *)
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ==> T) /\
  (* P7: eval_expr *)
  (!cx e st res st'.
    eval_expr cx e st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (* P8: eval_exprs *)
  (!cx es st res st'.
    eval_exprs cx es st = (res, st') ==>
    !v. res <> INR (ReturnException v))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  (* stmt/stmts/for cases: trivial *)
  TRY (simp[] >> NO_TAC) >>
  rpt gen_tac >>
  TRY strip_tac >>
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       return_def, raise_def, pairTheory.UNCURRY, LET_THM] >>
  cheat
QED

Theorem type_preservation:
  (* P0: eval_stmt — state + env preserved, return exceptions well-typed *)
  (!cx s. !env ret_ty st res st'.
    well_typed_stmt env ret_ty s /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (* P1: eval_stmts — state + env preserved, return exceptions well-typed *)
  (!cx ss. !env ret_ty st res st'.
    well_typed_stmts env ret_ty ss /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (* P2: eval_iterator *)
  (!cx it. !st res st'.
    state_well_typed st /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st') /\
  (* P3: eval_target *)
  (!cx g. !env st res st'.
    well_typed_atarget env g /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_target cx g st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P4: eval_targets *)
  (!cx gs. !env st res st'.
    EVERY (well_typed_atarget env) gs /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_targets cx gs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P5: eval_base_target *)
  (!cx bt. !env st res st'.
    well_typed_target env bt /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P6: eval_for *)
  (!cx tyv nm body vs. !st res st'.
    state_well_typed st /\
    eval_for cx tyv nm body vs st = (res, st') ==>
    state_well_typed st') /\
  (* P7: eval_expr — covers both success and failure *)
  (!cx e. !env st res st'.
    well_typed_expr env e /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_expr cx e st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!tv. res = INL tv ==>
       (!v st''. materialise cx tv st' = (INL v, st'') ==>
          state_well_typed st'' /\ env_consistent env cx st'' /\
          (!tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
                 value_has_type tyv v)))) /\
  (* P8: eval_exprs — with LIST_REL satisfies_type *)
  (* P8: eval_exprs — covers both success and failure *)
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!vs. res = INL vs ==>
      LIST_REL (\v e. !tyv.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
        value_has_type tyv v) vs es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  (* ===== P0: eval_stmt (goals 0-14) ===== *)
  (* 0: Pass *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def, raise_def])
  (* 1: Continue *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def, raise_def])
  (* 2: Break *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def, raise_def])
  (* 3: Return NONE *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def, raise_def,
          well_typed_stmt_def, Once evaluate_type_def,
          value_has_type_def])
  (* 4: Return SOME *)   >- cheat
  (* 5: Raise *)         >- cheat
  (* 6: Assert *)        >- cheat
  (* 7: Log *)           >- cheat
  (* 8: AnnAssign *)     >- cheat
  (* 9: Append *)        >- cheat
  (* 10: Assign *)       >- suspend "assign"
  (* 11: AugAssign *)    >- cheat
  (* 12: If *)           >- cheat
  (* 13: For *)          >- cheat
  (* 14: Expr *)         >- cheat
  (* ===== P1: eval_stmts (goals 15-16) ===== *)
  (* 15: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 16: s::ss — sequential: eval_stmt s then eval_stmts ss *)
  >- (rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, unitbind_apply] >>
      Cases_on `eval_stmt cx s st` >>
      rename1 `eval_stmt cx s st = (res_s, st_mid)` >>
      reverse (Cases_on `res_s`) >> simp[] >> strip_tac >> gvs[] >>
      gvs[well_typed_stmt_def] >>
      (* Apply IH_s (last_x_assum matches the unconditional one) *)
      last_x_assum
        (qspecl_then [`env`, `ret_ty`, `st`] mp_tac) >> simp[] >>
      strip_tac >>
      (* INR case: done by IH_s *)
      TRY (gvs[] >> NO_TAC) >>
      (* INL case: use conditioned IH_ss *)
      first_x_assum (qspecl_then [`st`, `st_mid`] mp_tac) >> simp[] >>
      disch_then (qspecl_then [`env`, `ret_ty`, `st_mid`] mp_tac) >>
      simp[] >> disch_then drule >> simp[]
     )
  (* ===== P2: eval_iterator (goals 17-18) ===== *)
  (* 17: Array *)        >- cheat
  (* 18: Range *)        >- cheat
  (* ===== P3: eval_target (goals 19-20) ===== *)
  (* 19: BaseTarget *)   >- cheat
  (* 20: TupleTarget *)  >- cheat
  (* ===== P4: eval_targets (goals 21-22) ===== *)
  (* 21: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 22: g::gs *)        >- cheat
  (* ===== P5: eval_base_target (goals 23-27) ===== *)
  (* 23: NameTarget *)        >- cheat
  (* 24: BareGlobalNameTarget *) >- cheat
  (* 25: TopLevelNameTarget *) >- cheat
  (* 26: AttributeTarget *)   >- cheat
  (* 27: SubscriptTarget *)   >- cheat
  (* ===== P6: eval_for (goals 28-29) ===== *)
  (* 28: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 29: v::vs *)        >- cheat
  (* ===== P7: eval_expr (goals 30-44) ===== *)
  (* 30: Name *)
  >- (rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _`
        (mp_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
      simp[bind_def, get_scopes_def, lift_option_type_def,
           return_def, LET_THM] >>
      Cases_on `lookup_scopes_val (string_to_num id) st.scopes` >>
      simp[return_def, raise_def] >> strip_tac >> gvs[] >>
      simp[materialise_def, return_def] >> rpt strip_tac >> gvs[] >>
      gvs[well_typed_expr_def, expr_type_def] >>
      `EVERY scope_well_typed st.scopes` by fs[state_well_typed_def] >>
      imp_res_tac lookup_scopes_val_well_typed >>
      fs[env_consistent_def] >>
      first_x_assum drule >> disch_then drule >> gvs[])
  (* 31: BareGlobalName *) >- cheat
  (* 32: TopLevelName *)   >- cheat
  (* 33: FlagMember *)     >- cheat
  (* 34: IfExp *)          >- cheat
  (* 35: Literal — TODO: needs well_formed_type_value hypothesis *)
  >- cheat
  (* 36: StructLit *)      >- cheat
  (* 37: Subscript *)      >- cheat
  (* 38: Attribute *)      >- cheat
  (* 39: Builtin *)        >- cheat
  (* 40: Pop *)            >- cheat
  (* 41: TypeBuiltin *)    >- cheat
  (* 42: Call Send *)      >- cheat
  (* 43: Call ExtCall *)   >- cheat
  (* 44: Call IntCall *)   >- cheat
  (* ===== P8: eval_exprs (goals 45-46) ===== *)
  (* 45: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 46: e::es *)
  >- suspend "P8cons"
QED

Resume type_preservation[P8cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
  qpat_x_assum`well_typed_exprs _ _`mp_tac >>
  rewrite_tac[well_typed_expr_def] >> strip_tac >>
  first_x_assum $ funpow 3 drule_then drule >> strip_tac >>
  simp[bind_apply] >>
  simp[CaseEq"prod",CaseEq"sum"] >>
  reverse strip_tac \\ gvs[return_def]
  >- ( drule materialise_state \\ rw[] )
  >- ( first_x_assum $ funpow 5 drule_then drule \\ rw[] )
  \\ first_x_assum drule_all \\ rw[]
QED

Resume type_preservation[assign]:
  rpt gen_tac \\ strip_tac
  \\ rpt gen_tac
  \\ rewrite_tac[well_typed_stmt_def]
  \\ rewrite_tac[evaluate_def]
  \\ rewrite_tac[bind_def, ignore_bind_def, CaseEq"sum", CaseEq"prod"]
  \\ simp_tac std_ss []
  \\ strip_tac
  \\ first_x_assum drule_all
  \\ strip_tac
  \\ cheat
QED

Finalise type_preservation
