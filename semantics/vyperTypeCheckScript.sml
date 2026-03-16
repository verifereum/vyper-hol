(*
 * vyperTypeCheckScript.sml
 *
 * Type system definitions and type soundness roadmap.
 *
 * TOP-LEVEL:
 *   satisfies_type     : value → type_value → bool  (value matches resolved type)
 *   scope_well_typed   : scope → bool               (all values in scope satisfy their types)
 *   state_well_typed   : evaluation_state → bool     (runtime state type invariant)
 *   type_preservation  : eval_expr preserves state_well_typed (CHEATED)
 *   no_type_errors     : well-typed state + valid program ⇒ no TypeError (CHEATED)
 *
 * Helper:
 *   is_numeric_type, is_int_type, is_bool_type, is_flag_type : type → bool
 *   well_typed_binop   : type → binop → type → type → bool
 *   well_typed_builtin_app : type → builtin → type list → bool
 *   well_typed_literal : type → literal → bool
 *   env_item_type, account_item_type : item → type
 *   well_formed_type   : (num |-> type_args) → type → bool
 *   all_satisfy_type, list_satisfies_type : list helpers for satisfies_type
 *
 * ROADMAP:
 *   Phase 1: Definitions (state_well_typed, well_formed_context)
 *   Phase 2: Preservation for pure operations (binop, builtin, literal helpers)
 *   Phase 3: Preservation for simple expressions (Name, Literal, IfExp, etc.)
 *   Phase 4: Preservation for builtins and subscripts
 *   Phase 5: Preservation for calls (requires stmt preservation)
 *   Phase 6: No-TypeError theorem
 *)

Theory vyperTypeCheck
Ancestors
  vyperAST vyperValue vyperMisc
  vyperInterpreter vyperState

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
  cheat
QED

(* TODO: evaluate_binop_satisfies_type
 *   Need to relate runtime type_values (tv1, tv2) back to syntactic types
 *   (t1, t2) used by well_typed_binop. Statement needs refinement once
 *   we work through the Literal and Name cases first.
 *)

(* Phase 3: Type preservation for simple expressions (TODO) *)

Theorem type_preservation:
  ∀cx e st v st' tv.
    state_well_typed st ∧
    eval_expr cx e st = (INL (Value v), st') ∧
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv
    ⇒ satisfies_type v tv ∧ state_well_typed st'
Proof
  (* By structural induction on e.
     Each case unfolds eval_expr one step and uses:
     - state_well_typed for variable lookups (Name, BareGlobalName)
     - Operation-level lemmas for Literal, Builtin
     - Inductive hypothesis for sub-expressions (IfExp, Subscript, etc.)
     Complex cases (Call) require proving eval_stmt preserves state_well_typed.
  *)
  cheat
QED

(* Phase 6: No-TypeError theorem (TODO) *)
(* TODO: define well_formed_context capturing static validity of cx
 *   - all referenced variables exist in scopes/immutables/storage
 *   - get_tenv cx is well-formed (struct/flag definitions resolve)
 *   - AST type annotations resolve (evaluate_type succeeds)
 *   - function signatures match their bodies
 *   - storage layout is consistent with declarations
 *)

Theorem no_type_errors:
  ∀cx e st msg st'.
    state_well_typed st ∧
    (* well_formed_context cx ∧ -- TODO: define this *)
    eval_expr cx e st = (INR (Error (TypeError msg)), st')
    ⇒ F
Proof
  (* Derived from type_preservation: each TypeError site in the interpreter
     corresponds to a type check that succeeds when state_well_typed holds
     and the program is well-formed. *)
  cheat
QED
