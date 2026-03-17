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
 *   type_preservation   : well_typed + consistent + eval ⇒ preserves types (36 CHEATS)
 *
 * PROOF STATUS:
 *   type_preservation has 47 inductive cases (from evaluate_ind).
 *   11 proved: Pass, Continue, Break, Return NONE, eval_stmts [],
 *   eval_stmts s::ss, eval_targets [], eval_for [], Name, Literal,
 *   eval_exprs [], eval_exprs e::es.
 *   36 cheated (see individual goal comments in proof).
 *
 * ===== TYPE SOUNDNESS ROADMAP =====
 *
 * NEXT STEP: Move this file to semantics/prop/vyperTypeSoundnessScript.sml
 *   and unify satisfies_type with value_has_type (from vyperTypingTheory).
 *
 *   value_has_type (in prop/vyperTypingScript.sml) is the correct typing
 *   predicate — it includes SArrayV canonicity (SORTED, keys < n, no
 *   default entries) and is used by the encode/decode roundtrip proof
 *   (in prop/vyperEncodeDecodeScript.sml), which is ALREADY FULLY PROVED.
 *
 *   satisfies_type (in this file) is a weaker duplicate that lacks
 *   canonicity. It should be deleted and replaced by value_has_type.
 *
 *   Migration steps:
 *     1. Move file to semantics/prop/vyperTypeSoundnessScript.sml
 *     2. Add vyperTyping, vyperEncodeDecode as ancestors
 *     3. Delete satisfies_type_def and all its helpers
 *     4. Rewrite state_well_typed, scope_well_typed, imms_well_typed
 *        to use value_has_type
 *     5. Update safe_cast bridge theorems for value_has_type
 *     6. Update all proved cases and helpers
 *
 * After migration, remaining work (ordered by risk):
 *
 * --- RISK 1: assign_subscripts preserves value_has_type ---
 * Risk: Deep recursive reasoning over nested subscript operations on
 *   arrays/structs/tuples. If the definition doesn't preserve the type
 *   invariant (e.g., inserting into sparse array breaks canonicity,
 *   replacing struct field changes key list), we'd need interpreter fixes.
 * Work:
 *   - Prove assign_subscripts tv v subs op = INL v' ∧
 *     value_has_type tv v ⇒ value_has_type tv v'
 *   - Handle each assign_op: Replace, Update, AppendOp, PopOp
 *
 * --- RISK 2: assign_target preserves storage_consistent ---
 * Risk: Combines roundtrip (already proved) with non-overlap layout
 *   property. well_formed_layout could be hard to state correctly
 *   (hashmap slots use keccak hashing — non-overlap is probabilistic).
 * Work:
 *   - Define storage_consistent cx st: for every storage variable,
 *     decode_value of its slot region produces a well-typed value.
 *     Separate predicate from state_well_typed (which doesn't take cx).
 *   - Define well_formed_layout cx: variable slot regions don't overlap.
 *   - Prove write_storage_slot preserves storage_consistent
 *     (from encode_decode_roundtrip_all + non-overlap)
 *   - Prove read_storage_slot returns well-typed values
 *   - Add storage_consistent + well_formed_layout to type_preservation
 *
 * --- RISK 3: Builtin operation type preservation ---
 * Risk: ~30 builtin operations, each needs its own lemma. Low risk per
 *   operation but high volume. Could discover operations whose semantics
 *   don't match the type system.
 * Work:
 *   - Per-operation value_has_type lemma (only Add/uint done so far)
 *   - Unlocks: Builtin(39) case of type_preservation
 *
 * --- RISK 4: ExtCall preserves storage_consistent ---
 * Risk: ExtCall replaces entire accounts + transient storage with the
 *   result of run_ext_call (opaque EVM execution). The returned state
 *   includes OUR contract's storage, which may have been modified by
 *   reentrant calls. storage_consistent for our contract could be
 *   violated. Proving preservation requires reasoning about EVM
 *   execution or Vyper's reentrancy guards. May need to assume
 *   storage_consistent as a postcondition, changing the theorem.
 * Work:
 *   - Determine if storage_consistent can be proved or must be assumed
 *   - Unlocks: Call ExtCall(43) case
 *
 * --- LOW RISK: remaining cases (do in any order) ---
 *
 * Mechanical delegation (goals 17-20, 22-27):
 *   Targets, iterators — just unfold and apply IH. ~12 cheats.
 *
 * Statement cases needing IH only (goals 4-7, 12, 14):
 *   Return SOME, Raise, Assert, Log, Expr, If.
 *   Need env_consistent through push/pop_scope.
 *
 * Assignment statement cases (goals 8-11, 13, 29):
 *   AnnAssign, Assign, AugAssign, Append, For.
 *   Need new_variable/assign_target preservation (from Risk 1-2 above).
 *   Need env_consistent through assignments.
 *
 * Expression cases (goals 31-34, 36-44):
 *   Each needs its own argument. IfExp(34) easy. BareGlobalName(31),
 *   TopLevelName(32) like Name but immutables/storage. Subscript(37),
 *   Attribute(38) need compound type reasoning. StructLit(36) needs
 *   struct construction. IntCall(44) has state preservation done
 *   (intcall_state_preserved), needs return value typing.
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
    (LENGTH al <= m /\
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

(* Helper: all_satisfy_type ↔ list_satisfies_type with REPLICATE *)
Theorem all_satisfy_list_satisfies:
  !vs tv. all_satisfy_type vs tv ==>
          list_satisfies_type vs (REPLICATE (LENGTH vs) tv)
Proof
  Induct >> REWRITE_TAC[satisfies_type_def] >>
  simp[rich_listTheory.REPLICATE] >>
  REWRITE_TAC[satisfies_type_def] >> metis_tac[]
QED

(* ZIP (MAP FST l, MAP SND l) = l *)
val zip_fst_snd = listTheory.ZIP_UNZIP
  |> ONCE_REWRITE_RULE[listTheory.UNZIP_MAP];

(*
 * Mutual induction using safe_cast_ind.
 * P0: safe_cast tv v = SOME v when satisfies_type v tv
 * P1: safe_cast_list tvs vs acc = SOME (REVERSE acc ++ vs)
 *     when list_satisfies_type vs tvs
 *)
Theorem safe_cast_satisfies_type_mutual:
  (!tv v. satisfies_type v tv ==> safe_cast tv v = SOME v) /\
  (!tvs vs acc.
     list_satisfies_type vs tvs ==>
     safe_cast_list tvs vs acc = SOME (REVERSE acc ++ vs))
Proof
  ho_match_mp_tac safe_cast_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  (* P0: main safe_cast case — case split on type and value *)
  >- (Cases_on `tv` >> Cases_on `v` >>
      TRY (Cases_on `b`) >>
      TRY (Cases_on `b'`) >>
      TRY (Cases_on `a`) >>
      REWRITE_TAC[satisfies_type_def] >>
      simp[Once safe_cast_def, compatible_bound_def] >>
      rpt strip_tac >> gvs[]
      (* SArrayV Fixed: safe_cast_list on MAP SND *)
      >- (imp_res_tac all_satisfy_list_satisfies >>
          `safe_cast_list (REPLICATE (LENGTH l) t) (MAP SND l) [] =
           SOME (MAP SND l)`
            by (first_x_assum irule >> gvs[listTheory.LENGTH_MAP]) >>
          simp[zip_fst_snd])
      (* DynArrayV *)
      >- (imp_res_tac all_satisfy_list_satisfies >>
          first_x_assum drule >> simp[])
      (* StructTV *)
      >- (`ZIP (MAP FST l, MAP SND l') = l'`
            by (qpat_x_assum `MAP FST l' = _` (SUBST1_TAC o SYM) >>
                simp[zip_fst_snd]) >>
          first_x_assum drule >> simp[])
     )
  (* P1: [] [] *)
  >- simp[Once safe_cast_def]
  (* P1: (t::ts) (v::vs) *)
  >- (strip_tac >>
      simp[Once safe_cast_def] >>
      gvs[Once satisfies_type_def] >>
      `safe_cast tv v = SOME v` by (first_x_assum irule >> simp[]) >>
      simp[] >>
      first_x_assum drule >> simp[])
  (* P1: mismatch (t::ts) [] — vacuous: list_satisfies_type [] _ = F *)
  >- gvs[Once satisfies_type_def]
  (* P1: mismatch [] (v::vs) — vacuous: list_satisfies_type _ [] = F *)
  >- gvs[Once satisfies_type_def]
QED

(* Corollary: safe_cast on well-typed value is identity *)
Theorem safe_cast_satisfies_type:
  !tv v. satisfies_type v tv ==> safe_cast tv v = SOME v
Proof
  metis_tac[safe_cast_satisfies_type_mutual]
QED

Theorem list_satisfies_replicate:
  !vs tv. list_satisfies_type vs (REPLICATE (LENGTH vs) tv) <=>
          all_satisfy_type vs tv
Proof
  Induct >> simp[Once satisfies_type_def, Once satisfies_type_def]
QED

Theorem list_satisfies_length:
  !vs tvs. list_satisfies_type vs tvs ==> LENGTH vs = LENGTH tvs
Proof
  Induct >> Cases_on `tvs` >>
  simp[Once satisfies_type_def] >> rpt strip_tac >> res_tac
QED

(* Converse: safe_cast success implies satisfies_type.
 * P1: safe_cast_list produces REVERSE acc ++ rs where
 * list_satisfies_type rs tvs. *)
Theorem safe_cast_implies_satisfies_type_mutual:
  (!tv v v'. safe_cast tv v = SOME v' ==> satisfies_type v' tv) /\
  (!tvs vs acc vs'.
     safe_cast_list tvs vs acc = SOME vs' ==>
     ?rs. vs' = REVERSE acc ++ rs /\ list_satisfies_type rs tvs)
Proof
  ho_match_mp_tac safe_cast_ind >>
  rpt conj_tac >> rpt gen_tac
  >- suspend "P0"
  >- suspend "P1_nil"
  >- suspend "P1_cons"
  >- simp[Once safe_cast_def]
  >- simp[Once safe_cast_def]
QED

Resume safe_cast_implies_satisfies_type_mutual[P0]:
  strip_tac >> rpt strip_tac >>
  pop_assum mp_tac >>
  simp[Once safe_cast_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[satisfies_type_def, compatible_bound_def] >>
  (* compound types: IH already applied by gvs, resolve ZIP/MAP algebra *)
  imp_res_tac list_satisfies_length >>
  gvs[GSYM list_satisfies_replicate, zip_fst_snd,
      listTheory.MAP_ZIP, listTheory.LENGTH_MAP,
      rich_listTheory.LENGTH_REPLICATE]
QED

Resume safe_cast_implies_satisfies_type_mutual[P1_nil]:
  strip_tac >> gvs[Once safe_cast_def] >>
  simp[Once satisfies_type_def]
QED

Resume safe_cast_implies_satisfies_type_mutual[P1_cons]:
  strip_tac >>
  simp[Once safe_cast_def, AllCaseEqs()] >>
  rpt strip_tac >>
  rename1 `safe_cast tv v = SOME cv` >>
  `satisfies_type cv tv` by res_tac >>
  (* IH for tail *)
  last_x_assum (qspec_then `cv` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  simp[Once satisfies_type_def]
QED

Finalise safe_cast_implies_satisfies_type_mutual

Theorem safe_cast_implies_satisfies_type:
  !tv v v'. safe_cast tv v = SOME v' ==> satisfies_type v' tv
Proof
  metis_tac[safe_cast_implies_satisfies_type_mutual]
QED

(* KEY LEMMA: bind_arguments produces a well-typed scope.
 * No precondition on input values needed — safe_cast inside
 * bind_arguments guarantees satisfies_type for stored values. *)
Theorem bind_arguments_scope_well_typed:
  !tenv params vs sc.
    bind_arguments tenv params vs = SOME sc ==>
    scope_well_typed sc
Proof
  MAP_EVERY qid_spec_tac [`sc`, `vs`, `params`, `tenv`] >>
  Induct_on `params`
  (* base: [] *)
  >- (rpt gen_tac >>
      Cases_on `vs` >>
      simp[Once bind_arguments_def, scope_well_typed_def,
           finite_mapTheory.FLOOKUP_EMPTY]) >>
  (* cons *)
  simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >>
  Cases_on `vs` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  `scope_well_typed m`
    by (first_x_assum (qspecl_then [`tenv`, `t`, `m`] mp_tac) >>
        gvs[]) >>
  imp_res_tac safe_cast_implies_satisfies_type >>
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
    !src_id_opt fn ts fm args dflts ret body.
      get_module_code cx src_id_opt = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts =
        SOME (fm, args, dflts, ret, body) ==>
      ?env_body ret_tv.
        env_body.type_defs = get_tenv cx /\
        env_body.global_types = FEMPTY /\
        evaluate_type (get_tenv cx) ret = SOME ret_tv /\
        well_typed_stmts env_body ret body /\
        well_typed_exprs
          <| var_types := FEMPTY;
             global_types := FEMPTY;
             toplevel_types := FEMPTY;
             type_defs := get_tenv cx |> dflts /\
        (!id typ. MEM (id, typ) args ==>
           FLOOKUP env_body.var_types (string_to_num id) = SOME typ)
End

(* Separate predicate: call site type annotations match function return types *)

Theorem env_consistent_empty:
  !cx st.
    env_consistent
      <| var_types := FEMPTY;
         global_types := FEMPTY;
         toplevel_types := FEMPTY;
         type_defs := get_tenv cx |> cx st
Proof
  simp[env_consistent_def, finite_mapTheory.FLOOKUP_EMPTY]
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

Theorem functions_well_typed_stk_irrelevant:
  !cx f. functions_well_typed (cx with stk updated_by f) <=>
         functions_well_typed cx
Proof
  simp[functions_well_typed_def, get_module_code_def,
       get_tenv_stk_irrelevant]
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
  simp[push_function_def, return_def, state_well_typed_def] >>
  rpt strip_tac >> gvs[]
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
       state_well_typed_def] >>
  rpt strip_tac >> gvs[]
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
  simp[pop_function_def, set_scopes_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

(* push_function preserves immutables *)
Theorem push_function_immutables:
  !src_fn sc cx st cxf st'.
    push_function src_fn sc cx st = (INL cxf, st') ==>
    st'.immutables = st.immutables
Proof
  simp[push_function_def, return_def] >> rpt strip_tac >> gvs[]
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

(* Helper: state_well_typed is preserved through IntCall.
   Takes simplified IHs as hypotheses. *)
Theorem intcall_state_preserved:
  !cx src_id_opt fn es v17 env st v st' tv.
    (* IH for eval_exprs cx es (args) *)
    (!env0 st0 vs0 st0'.
       well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
       state_well_typed st0 /\ functions_well_typed cx /\
       eval_exprs cx es st0 = (INL vs0, st0') ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       LIST_REL (\v e. !tyv.
         evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
         satisfies_type v tyv) vs0 es) /\
    (* IH for eval_exprs cxd needed_dflts (defaults) *)
    (!dflts_sub env0 st0 vs0 st0'.
       well_typed_exprs env0 dflts_sub /\
       env_consistent env0 (cx with stk updated_by CONS (src_id_opt, fn)) st0 /\
       state_well_typed st0 /\
       functions_well_typed (cx with stk updated_by CONS (src_id_opt, fn)) /\
       eval_exprs (cx with stk updated_by CONS (src_id_opt, fn))
         dflts_sub st0 = (INL vs0, st0') ==>
       state_well_typed st0' /\
       LIST_REL (\v e. !tyv.
         evaluate_type (get_tenv (cx with stk updated_by CONS (src_id_opt, fn)))
           (expr_type e) = SOME tyv ==>
         satisfies_type v tyv) vs0 dflts_sub) /\
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
    (last_x_assum (qspecl_then [`env`, `s''`, `vs`, `s'⁴'`] mp_tac) >>
     simp[]) >>
  (* Destructure fn_info *)
  PairCases_on `fn_info` >> gvs[] >>
  (* Step 2: Apply IH_dflts *)
  `functions_well_typed (cx with stk updated_by CONS (src_id_opt, fn))` by
    gvs[functions_well_typed_stk_irrelevant] >>
  `well_typed_exprs
     <|var_types := FEMPTY; global_types := FEMPTY;
       toplevel_types := FEMPTY; type_defs := get_tenv cx|> fn_info2` by
    (qpat_x_assum `functions_well_typed cx` mp_tac >>
     simp[functions_well_typed_def] >>
     disch_then (qspecl_then
       [`src_id_opt`, `fn`, `ts`, `fn_info0`, `fn_info1`,
        `fn_info2`, `fn_info3`, `fn_info4`]
       mp_tac) >> simp[] >> strip_tac >> simp[]) >>
  rename1 `eval_exprs _ (DROP drop_n _) s'⁴' = (INL dflt_vs, s'⁵')` >>
  `well_typed_exprs
     <|var_types := FEMPTY; global_types := FEMPTY;
       toplevel_types := FEMPTY; type_defs := get_tenv cx|>
     (DROP drop_n fn_info2)` by
    (irule well_typed_exprs_DROP >> gvs[]) >>
  `state_well_typed s'⁵'` by
    (qpat_x_assum `!dflts_sub env0 st0 vs0 st0'. _`
       (qspecl_then
          [`DROP drop_n fn_info2`,
           `<|var_types := FEMPTY; global_types := FEMPTY;
              toplevel_types := FEMPTY;
              type_defs := get_tenv cx|>`,
           `s'⁴'`, `dflt_vs`, `s'⁵'`] mp_tac) >>
     impl_tac >- (
       simp[get_tenv_stk_irrelevant] >>
       simp[env_consistent_def, finite_mapTheory.FLOOKUP_EMPTY,
            get_tenv_stk_irrelevant]
     ) >> simp[]) >>
  (* Extract well_typed_stmts from functions_well_typed *)
  `?env_body.
     env_body.type_defs = get_tenv cx /\
     env_body.global_types = FEMPTY /\
     well_typed_stmts env_body fn_info3 fn_info4 /\
     (!id typ. MEM (id, typ) fn_info1 ==>
        FLOOKUP env_body.var_types (string_to_num id) = SOME typ)` by
    (qpat_x_assum `functions_well_typed cx` mp_tac >>
     simp[functions_well_typed_def] >>
     disch_then (qspecl_then
       [`src_id_opt`, `fn`, `ts`, `fn_info0`, `fn_info1`,
        `fn_info2`, `fn_info3`, `fn_info4`] mp_tac) >>
     simp[] >> strip_tac >> qexists_tac `env_body` >> simp[]) >>
  (* state_well_typed for callee entry state *)
  `state_well_typed (s'⁵' with scopes := [sc])` by
    (simp[state_well_typed_def] >> gvs[state_well_typed_def] >>
     (* scope_well_typed sc: follows directly from bind_arguments success *)
     drule bind_arguments_scope_well_typed >> simp[]) >>
  (* env_consistent for callee *)
  `env_consistent env_body
     (cx with stk updated_by CONS (src_id_opt, fn))
     (s'⁵' with scopes := [sc])` by
    (mp_tac (Q.SPECL [`get_tenv cx`, `fn_info1`, `vs ++ dflt_vs`, `sc`,
                       `env_body`,
                       `cx with stk updated_by CONS (src_id_opt, fn)`,
                       `s'⁵'`]
               bind_arguments_env_consistent) >>
     simp[get_tenv_stk_irrelevant]) >>
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
    gvs[state_well_typed_def]
  )
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

Theorem unitbind_apply:
  !f g s. (do f; g od) s =
    case f s of (INL x,s') => g s' | (INR e,s') => (INR e,s')
Proof
  EVAL_TAC >> simp[bind_def]
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
                satisfies_type v ret_tv)) /\
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
                satisfies_type v ret_tv)) /\
  (* P2: eval_iterator *)
  (!cx it. !st res st'.
    state_well_typed st /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st') /\
  (* P3: eval_target *)
  (!cx g. !st res st'.
    state_well_typed st /\
    eval_target cx g st = (res, st') ==>
    state_well_typed st') /\
  (* P4: eval_targets *)
  (!cx gs. !st res st'.
    state_well_typed st /\
    eval_targets cx gs st = (res, st') ==>
    state_well_typed st') /\
  (* P5: eval_base_target *)
  (!cx bt. !st res st'.
    state_well_typed st /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st') /\
  (* P6: eval_for *)
  (!cx tyv nm body vs. !st res st'.
    state_well_typed st /\
    eval_for cx tyv nm body vs st = (res, st') ==>
    state_well_typed st') /\
  (* P7: eval_expr — general form covering all typed_value results *)
  (!cx e. !env st tv st'.
    well_typed_expr env e /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_expr cx e st = (INL tv, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!v st''. materialise cx tv st' = (INL v, st'') ==>
       state_well_typed st'' /\ env_consistent env cx st'' /\
       (!tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
              satisfies_type v tyv))) /\
  (* P8: eval_exprs — with LIST_REL satisfies_type *)
  (!cx es. !env st vs st'.
    well_typed_exprs env es /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_exprs cx es st = (INL vs, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    LIST_REL (\v e. !tyv.
      evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
      satisfies_type v tyv) vs es)
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
          satisfies_type_def])
  (* 4: Return SOME *)   >- cheat
  (* 5: Raise *)         >- cheat
  (* 6: Assert *)        >- cheat
  (* 7: Log *)           >- cheat
  (* 8: AnnAssign *)     >- cheat
  (* 9: Append *)        >- cheat
  (* 10: Assign *)       >- cheat
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
  (* 35: Literal *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def] >>
      simp[materialise_def, return_def] >> rpt strip_tac >> gvs[] >>
      gvs[well_typed_expr_def, expr_type_def] >>
      metis_tac[evaluate_literal_satisfies_type])
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
  >- (rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_exprs _ _ _ = _`
        (mp_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
      simp[bind_def, AllCaseEqs()] >> strip_tac >>
      (* Now have: eval_expr cx e st = (INL tv, s1) /\
                   materialise cx tv s1 = (INL v_hd, s2) /\
                   eval_exprs cx es s2 = (INL vs_tl, s3) /\
                   return (v_hd::vs_tl) s3 = (INL vs, st') *)
      gvs[return_def, well_typed_expr_def] >>
      (* P7 IH *)
      qpat_x_assum `!env0 st0 tv0 st0'. well_typed_expr _ _ /\ _ ==> _`
        (drule_at (Pos last)) >>
      disch_then (qspec_then `env` mp_tac) >> simp[] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      (* P8 IH — match materialise in assumptions *)
      first_x_assum drule_all >> simp[]
    )
QED
