(*
 * Type system definitions and type soundness proof infrastructure.
 *
 * TOP-LEVEL:
 *   typing_env          : static type environment (var_types, global_types, etc.)
 *   well_typed_expr     : typing_env → expr → bool (static type consistency)
 *   well_typed_stmt     : typing_env → ty → stmt → bool
 *   env_consistent      : typing_env → cx → st → bool (env matches runtime state)
 *   state_well_typed    : evaluation_state → bool (runtime values satisfy stored types)
 *   functions_well_typed: cx → bool (callable functions have well-typed bodies)
 *   type_preservation   : well_typed + consistent + eval ⇒ preserves types
 *
 * KEY HELPERS (proved):
 *   assign_target_well_typed    : assign_target preserves state_well_typed + env_consistent
 *   assign_target_no_return     : assign_target never returns ReturnException
 *   evaluate_no_return          : eval_expr and related never return ReturnException
 *   eval_base_target_type_connection : connects AST target type to runtime type
 *   IntCall (suspension)        : internal call type preservation (WIP)
 *   set_immutable_well_typed    : set_immutable preserves state_well_typed + env_consistent
 *   set_global_well_typed       : set_global preserves state_well_typed + env_consistent
 *   write_storage_slot_well_typed : storage writes preserve state_well_typed + env_consistent
 *   (uses value_has_type from vyperTypingTheory for value/type compatibility)
 *   (uses assign_subscripts_preserves_type from vyperAssignPreservesTypeTheory)
 *
 * PROOF STATUS:
 *   type_preservation: 14/47 cases proved, 33 cheated.
 *     Proved: 0-3 (Pass/Continue/Break/Return NONE), 10 (Assign),
 *             15-16 (eval_stmts), 21 (eval_targets []), 28 (eval_for []),
 *             30 (Name), 45-46 (eval_exprs)
 *
 * REMAINING CHEATS (33, ordered by risk):
 *
 * --- HIGH RISK: complex control flow ---
 *   44: Call IntCall — function lookup, push/pop scope, bind_arguments,
 *       recursive eval_stmts, return value handling
 *   13: For — eval_iterator + eval_for with scope manipulation
 *   29: eval_for v::vs — new_variable, eval_stmts body, Continue/Break
 *
 * --- MEDIUM RISK: need evaluate_type propagation (validates existential P7) ---
 *   37: Subscript — subscript_type_ok must preserve evaluate_type success
 *   38: Attribute — attribute_type_ok must preserve evaluate_type success
 *   36: StructLit — struct type evaluation
 *
 * --- MEDIUM RISK: builtin/call operations ---
 *   39: Builtin — ~30 builtin ops, each needs value_has_type lemma
 *   40: Pop, 41: TypeBuiltin — array/type operations
 *   42: Call Send, 43: Call ExtCall — external interactions
 *
 * --- LOW RISK: simple control flow (use IH directly) ---
 *   4: Return SOME, 5: Raise, 6: Assert, 7: Log, 14: Expr
 *   8: AnnAssign, 9: Append, 11: AugAssign, 12: If
 *
 * --- LOW RISK: mechanical (read-only state preservation) ---
 *   17-18: eval_iterator (Array, Range)
 *   19-20: eval_target (BaseTarget, TupleTarget)
 *   22: eval_targets (g::gs)
 *   23-27: eval_base_target (5 constructor cases)
 *
 * --- LOW RISK: expr cases similar to proved Name case ---
 *   31: BareGlobalName, 32: TopLevelName, 33: FlagMember
 *   34: IfExp, 35: Literal
 *)

Theory vyperTypeSoundness
Ancestors
  list rich_list pred_set prim_rec sorting relation
  finite_map combin option pair
  vyperAST vyperValue vyperValueOperation vyperMisc
  vyperInterpreter vyperState vyperContext
  vyperStatePreservation vyperScopePreservation
  vyperLookup vyperImmutablesPreservation
  vyperEvalPreservesScopes
  vyperTyping vyperEncodeDecode vyperAssignPreservesType

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
    (is_flag_type ty /\
     well_formed_type env.type_defs ty) /\
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
     well_formed_type env.type_defs ty) /\
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
  well_typed_expr env (TypeBuiltin ty _ target_ty es) =
    (well_typed_exprs env es /\
     well_formed_type env.type_defs ty /\
     well_formed_type env.type_defs target_ty) /\
  well_typed_expr env (Pop ty tgt) =
    (?arr_ty. well_typed_target env tgt arr_ty /\
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
  well_typed_iterator env (Array e) = well_typed_expr env e /\
  well_typed_iterator env (Range e1 e2) =
    (well_typed_expr env e1 /\ well_typed_expr env e2)
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
    (?arr_ty. well_typed_target env bt arr_ty /\
     well_typed_expr env e) /\
  well_typed_stmt env ret_ty (Assign tgt e) =
    (well_typed_atarget env tgt (expr_type e) /\
     well_typed_expr env e) /\
  well_typed_stmt env ret_ty (AugAssign ty bt bop e) =
    (well_typed_target env bt ty /\
     well_typed_expr env e /\
     well_formed_type env.type_defs ty) /\
  well_typed_stmt env ret_ty (If e ss1 ss2) =
    (well_typed_expr env e /\
     expr_type e = BaseT BoolT /\
     well_typed_stmts env ret_ty ss1 /\
     well_typed_stmts env ret_ty ss2) /\
  well_typed_stmt env ret_ty (For id typ it n body) =
    (well_formed_type env.type_defs typ /\
     well_typed_iterator env it /\
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

(* Helper: env_consistent survives popping a scope when going from
   extended env back to outer env *)
Theorem env_consistent_pop_scope:
  !env nm typ cx st.
    env_consistent (env with var_types updated_by flip $|+ (nm, typ)) cx st /\
    st.scopes <> [] /\
    nm NOTIN FDOM env.var_types /\
    (!id. id IN FDOM (HD st.scopes) /\ id <> nm ==>
          lookup_scopes id (TL st.scopes) = NONE)
    ==>
    env_consistent env cx (st with scopes := TL st.scopes)
Proof
  rpt strip_tac >>
  fs[env_consistent_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  (* var_types conjunct *)
  >- (
    rpt strip_tac >>
    `id <> nm` by (strip_tac >> gvs[finite_mapTheory.FLOOKUP_DEF]) >>
    Cases_on `id IN FDOM (HD st.scopes)`
    >- (first_x_assum drule >> simp[] >> strip_tac >> gvs[]) >>
    last_x_assum irule >>
    qexists_tac`id` >> rw[] >>
    Cases_on`st.scopes` >>
    gvs[lookup_scopes_def, FLOOKUP_DEF]) >>
  (* global_types conjunct *)
  rpt strip_tac >> res_tac
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
  \\ gvs[bind_apply, AllCaseEqs(), bound_CASE_rator, ignore_bind_apply,
         return_def, check_def, assert_def, raise_def]
  \\ first_x_assum irule
  \\ TRY(qexists_tac`0` \\ simp[] \\ goal_assum drule)
  \\ qexists_tac`1` \\ simp[]
  \\ gvs[wordsTheory.word_add_n2w]
  \\ goal_assum drule
QED

Theorem materialise_error:
  materialise a b c = (INR e, s) ==>
  ?m. e = Error m
Proof
  Cases_on`b` \\ rw[materialise_def, return_def, raise_def, bind_apply]
  \\ gvs[AllCaseEqs()]
  \\ drule read_storage_slot_error \\ rw[]
QED

Theorem get_Value_error:
  get_Value a b = (INR e, s) ==>
  e = Error (TypeError "not Value")
Proof
  Cases_on`a` \\ rw[get_Value_def, return_def, raise_def]
QED

Theorem lookup_flag_mem_error:
  lookup_flag_mem cx nsid mid st = (INR e, s) ==>
  ?m. e = Error (TypeError m)
Proof
  Cases_on `nsid`
  \\ rw[lookup_flag_mem_def, option_CASE_rator, AllCaseEqs(),
        return_def, raise_def]
QED

Theorem check_array_bounds_error:
  check_array_bounds cx tv v st = (INR e, s) ==>
  ?m. e = Error m
Proof
  rw[oneline check_array_bounds_def, bind_apply, AllCaseEqs(),
     value_CASE_rator, toplevel_value_CASE_rator, return_def,
     bound_CASE_rator]
  \\ gvs[check_def, assert_def, raise_def]
QED

Theorem get_accounts_no_error[simp]:
  get_accounts st <> (INR e, s)
Proof
  rw[get_accounts_def, return_def]
QED

Theorem toplevel_array_length_error:
  toplevel_array_length cx tv st = (INR e, s) ==>
  ?m. e = Error (TypeError m)
Proof
  rw[oneline toplevel_array_length_def, bind_apply, AllCaseEqs(),
     toplevel_value_CASE_rator, value_CASE_rator, array_value_CASE_rator,
     bound_CASE_rator, return_def, raise_def]
QED

Theorem transfer_value_error:
  transfer_value a b c d = (INR e, s) ==>
  ?m. e = Error m
Proof
  rw[transfer_value_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
     return_def, raise_def, check_def, assert_def,
     update_accounts_def, get_accounts_def]
QED

Theorem switch_BoolV_error:
  switch_BoolV v f g st = (INR e, s) ==>
  f st <> (INR e, s) /\ g st <> (INR e, s) ==>
  ?m. e = Error m
Proof
  rw[switch_BoolV_def, raise_def]
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
           bind_apply, ignore_bind_apply]
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
  (* ImmutableVar *)
  \\ conj_tac >- (
    rw[assign_target_def, bind_apply, AllCaseEqs()]
    \\ TRY (drule get_immutables_error \\ rw[])
    \\ TRY (drule lift_option_type_error \\ rw[])
    \\ TRY (drule lift_sum_error \\ rw[])
    \\ gvs[set_immutable_def, bind_apply, AllCaseEqs(),
           set_address_immutables_def, return_def,
           get_address_immutables_def, ignore_bind_apply]
    \\ TRY (drule lift_option_error \\ rw[])
    \\ strip_tac \\ gvs[]
    \\ drule assign_result_error \\ rw[])
  (* TupleTargetV Replace (ArrayV (TupleV vs)) *)
  \\ conj_tac >- (
    rw[assign_target_def, bind_apply, AllCaseEqs(), ignore_bind_apply,
       assert_def, return_def]
    \\ strip_tac \\ gvs[type_check_def, assert_def]
    \\ first_x_assum drule \\ rw[])
  (* remaining catch-alls + assign_targets *)
  \\ simp[assign_target_def, raise_def, return_def, bind_apply,
          AllCaseEqs(), ignore_bind_apply, assert_def]
  \\ rpt strip_tac \\ gvs[]
  \\ first_x_assum drule \\ gvs[]
QED

(*
Theorem assign_targets_well_typed:
  !cx gvs vs st res st' env.
    assign_targets cx gvs vs st = (res, st') /\
    state_well_typed st /\ env_consistent env cx st /\
    LIST_REL (\gv v. !st res st'.
      assign_target cx gv (Replace v) st = (res, st') /\
      state_well_typed st /\ env_consistent env cx st ==>
      state_well_typed st' /\ env_consistent env cx st') gvs vs ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  Induct_on`gvs` \\ simp[assign_target_def, return_def]
  \\ rpt gen_tac \\ strip_tac
  \\ BasicProvers.VAR_EQ_TAC
  \\ qhdtm_x_assum`assign_targets`mp_tac
  \\ simp_tac std_ss [assign_target_def]
  \\ simp_tac std_ss [ignore_bind_apply, AllCaseEqs()]
  \\ reverse strip_tac
  \\ first_x_assum drule
  >- ( last_x_assum kall_tac \\ gvs[] )
  \\ first_x_assum drule
  \\ ntac 2 strip_tac \\ gvs[]
  \\ first_x_assum drule
  \\ gvs[]
QED
*)

(* TODO: move *)
Theorem eval_targets_length:
  !a b c d e.
  eval_targets a b c = (INL d, e)
  ==> LENGTH b = LENGTH d
Proof
  Induct_on`b` \\ rw[evaluate_def, return_def]
  \\ gvs[bind_apply, AllCaseEqs(), return_def]
  \\ first_x_assum drule \\ rw[]
QED

Theorem values_have_types_LIST_REL:
  !tys tvs. values_have_types tys tvs =
  LIST_REL value_has_type tys tvs
Proof
  Induct \\ rw[value_has_type_def]
  \\ Cases_on`tvs` \\ gvs[value_has_type_def]
QED

Theorem set_global_well_typed:
  !cx src n v st res st' env.
    set_global cx src n v st = (res, st') /\
    state_well_typed st /\ env_consistent env cx st ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  rpt strip_tac
  >> imp_res_tac set_global_scopes
  >> imp_res_tac set_global_immutables
  >> gvs[state_well_typed_def, env_consistent_def]
  >> metis_tac[]
QED

Theorem write_storage_slot_well_typed:
  !cx is_trans slot tv v st res st' env.
    write_storage_slot cx is_trans slot tv v st = (res, st') /\
    state_well_typed st /\ env_consistent env cx st ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  rpt strip_tac
  >> imp_res_tac write_storage_slot_scopes
  >> imp_res_tac write_storage_slot_immutables
  >> gvs[state_well_typed_def, env_consistent_def]
  >> metis_tac[]
QED

Theorem set_immutable_error_state:
  !cx src n tv v st e st'.
    set_immutable cx src n tv v st = (INR e, st') ==> st' = st
Proof
  rw[set_immutable_def, bind_apply, AllCaseEqs(),
     get_address_immutables_def, set_address_immutables_def,
     return_def]
  >> imp_res_tac lift_option_state >> simp[]
QED

Theorem set_immutable_well_typed:
  !cx src n tv v st st' env.
    set_immutable cx src n tv v st = (INL (), st') /\
    state_well_typed st /\ env_consistent env cx st /\
    value_has_type tv v /\
    (?old_v. FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of
         SOME m => m | NONE => [])) n = SOME (tv, old_v)) ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  simp[set_immutable_def]
  \\ rpt gen_tac
  \\ simp[bind_apply, AllCaseEqs()]
  \\ strip_tac
  \\ gvs[set_address_immutables_def, return_def]
  \\ gvs[state_well_typed_def, env_consistent_def]
  \\ gvs[get_address_immutables_def, lift_option_def]
  \\ gvs[AllCaseEqs(), option_CASE_rator, raise_def, return_def]
  \\ gvs[EVERY_MEM, alistTheory.MEM_ADELKEY, pairTheory.FORALL_PROD]
  \\ gvs[get_source_immutables_def, set_source_immutables_def]
  \\ gvs[alistTheory.ALOOKUP_ADELKEY]
  \\ gvs[imms_well_typed_def]
  \\ rw[]
  \\ gvs[finite_mapTheory.FLOOKUP_UPDATE, CaseEq"bool"]
  \\ gvs[alistTheory.ALOOKUP_ADELKEY]
  \\ res_tac
  \\ last_x_assum irule
  \\ goal_assum $ drule_at Any
  \\ TRY CASE_TAC \\ gvs[]
  \\ goal_assum drule
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ goal_assum drule
QED

(* loc_type: the runtime type stored at a target location *)
Definition loc_type_def:
  loc_type cx st (ScopedVar s) tv =
    (?a. lookup_scopes (string_to_num s) st.scopes = SOME (tv, a)) /\
  loc_type cx st (ImmutableVar s) tv =
    (?imms a. get_immutables cx (current_module cx) st = (INL imms, st) /\
              FLOOKUP imms (string_to_num s) = SOME (tv, a)) /\
  loc_type cx st (TopLevelVar src s) tv = F
End

(* TODO: move *)

Theorem leaf_type_NoneTV[simp]:
  leaf_type NoneTV x = NoneTV
Proof
  Cases_on`x` \\ rw[leaf_type_def]
QED

(* Connection between AST target type and runtime leaf type.
   For a base target b with type ty, if eval_base_target returns (loc, sbs),
   and the base variable at loc has runtime type tv (connected via
   env_consistent), then evaluate_type ty = leaf_type tv (REVERSE sbs). *)
Theorem evaluate_type_mono:
  (!tenv ty tv k.
    evaluate_type (tenv \\ k) ty = SOME tv ==>
    evaluate_type tenv ty = SOME tv) /\
  (!tenv ts acc tvs k.
    evaluate_types (tenv \\ k) ts acc = SOME tvs ==>
    evaluate_types tenv ts acc = SOME tvs)
Proof
  ho_match_mp_tac evaluate_type_ind
  (* BaseT *)
  >> conj_tac >- simp[evaluate_type_def]
  (* TupleT *)
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    first_x_assum drule >> simp[])
  (* ArrayT *)
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    first_x_assum drule >> simp[])
  (* StructT *)
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs(), DOMSUB_FLOOKUP_THM, DOMSUB_COMMUTES] >>
    first_x_assum drule >>
    strip_tac \\ goal_assum drule >> gvs[])
  (* FlagT *)
  >> conj_tac >- (
    rpt gen_tac >> rpt gen_tac >>
    simp[evaluate_type_def, AllCaseEqs(), DOMSUB_FLOOKUP_THM] >>
    rpt strip_tac >> gvs[])
  (* NoneT *)
  >> conj_tac >- simp[evaluate_type_def]
  (* evaluate_types [] *)
  >> conj_tac >- simp[evaluate_type_def]
  (* evaluate_types cons *)
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum (fn th => drule (cj 1 th)) >> strip_tac >> simp[] >>
  first_x_assum drule >> simp[] >>
  disch_then irule >> goal_assum drule
QED

Theorem leaf_type_append:
  !tv subs1 subs2. leaf_type tv (subs1 ++ subs2) = leaf_type (leaf_type tv subs1) subs2
Proof
  ho_match_mp_tac leaf_type_ind
  \\ rw[leaf_type_def]
  >> CASE_TAC >> gvs[leaf_type_def]
QED

Theorem eval_base_target_type_connection:
  !b cx st0 loc sbs st1 env st ty tv.
    eval_base_target cx b st0 = (INL (loc, sbs), st1) /\
    well_typed_target env b ty /\
    env_consistent env cx st /\
    loc_type cx st loc tv ==>
    ?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\
          tyv = leaf_type tv (REVERSE sbs) /\
          well_formed_type_value tv
Proof
  Induct
  (* NameTarget *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_apply, AllCaseEqs(), ignore_bind_apply,
          get_scopes_def, return_def, type_check_def, assert_def,
          well_typed_expr_def, loc_type_def, leaf_type_def] >>
      gvs[env_consistent_def] >>
      first_x_assum drule >>
      disch_then drule >> simp[] >>
      MATCH_ACCEPT_TAC (cj 1 evaluate_type_well_formed))
  (* BareGlobalNameTarget *)
  >- (
    simp[Once evaluate_def, bind_apply, AllCaseEqs(), ignore_bind_apply,
         return_def, type_check_def, assert_def, option_CASE_rator,
         well_typed_expr_def, loc_type_def, leaf_type_def,
         get_immutables_def, get_address_immutables_def, lift_option_def,
         optionTheory.IS_SOME_EXISTS, pairTheory.EXISTS_PROD]
    >> rpt gen_tac
    >> strip_tac >> gvs[env_consistent_def, raise_def, return_def]
    >> first_assum $ drule_then (irule_at(Pos(el 1)))
    >> gvs[loc_type_def, leaf_type_def]
    >> gvs[get_immutables_def, bind_apply, AllCaseEqs(), return_def]
    >> gvs[get_address_immutables_def, lift_option_def, return_def]
    >> gvs[AllCaseEqs(), option_CASE_rator, raise_def, return_def]
    >> irule (cj 1 evaluate_type_well_formed)
    >> first_x_assum(drule_at_then Any drule)
    >> strip_tac
    >> goal_assum drule )
  (* TopLevelNameTarget *)
  >- (
    simp[pairTheory.FORALL_PROD] >>
    rw[Once evaluate_def, return_def, well_typed_expr_def, loc_type_def]
    >> gvs[loc_type_def] )
  (* SubscriptTarget *)
  >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
        well_typed_expr_def, loc_type_def,
        bind_def, option_CASE_rator] >>
    pairarg_tac \\ gvs[bind_apply, AllCaseEqs(),return_def, leaf_type_append]
    >> first_x_assum drule_all >> strip_tac >>
    gvs[lift_option_type_def, option_CASE_rator, AllCaseEqs(), raise_def]
    >> gvs[return_def] >>
    Cases_on`tgt_ty` >> gvs[subscript_type_ok_def] >>
    gvs[Once evaluate_type_def] >>
    gvs[CaseEq"option"] >>
    qpat_x_assum`_ = leaf_type _ _`(SUBST_ALL_TAC o SYM) >>
    simp[leaf_type_def])
  (* AttributeTarget *)
  >> (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
        well_typed_expr_def, loc_type_def] >>
    gvs[bind_def, AllCaseEqs()] >>
    pairarg_tac >> gvs[return_def] >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on`tgt_ty` >>
    gvs[attribute_type_ok_def, leaf_type_def] >>
    gvs[leaf_type_append, leaf_type_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[evaluate_type_def] >>
    gvs[AllCaseEqs()] >>
    qpat_x_assum`StructTV _ = leaf_type _ _`(assume_tac o SYM) >>
    gvs[leaf_type_def, env_consistent_def] >>
    gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
    simp[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
    simp[pairTheory.LAMBDA_PROD, alistTheory.ALOOKUP_MAP] >>
    gvs[EVERY_MAP] >>
    drule alistTheory.ALOOKUP_MEM >>
    gvs[EVERY_MEM] >>
    strip_tac \\ first_x_assum drule >>
    rw[optionTheory.IS_SOME_EXISTS] >> rw[] >>
    irule (cj 1 evaluate_type_mono) >>
    goal_assum drule)
QED

Theorem assign_target_well_typed:
  (!g. !cx tgt st0 st1 v st res st' env ty.
    eval_target cx g st0 = (INL tgt, st1) /\
    well_typed_atarget env g ty /\
    assign_target cx tgt (Replace v) st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    (?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\
           value_has_type tyv v) ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (!gs. !cx gvs st0 st1 vs st res st' env tys.
    eval_targets cx gs st0 = (INL gvs, st1) /\
    LIST_REL (well_typed_atarget env) gs tys /\
    assign_targets cx gvs vs st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    LIST_REL (\ty v. ?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\
              value_has_type tyv v) tys vs ==>
    state_well_typed st' /\ env_consistent env cx st')
Proof
  ho_match_mp_tac assignment_target_induction
  \\ conj_tac
  >- (
    simp[evaluate_def]
    \\ rpt gen_tac
    \\ simp[bind_def, CaseEq"prod", CaseEq"sum"]
    \\ strip_tac
    \\ pairarg_tac \\ gvs[return_def]
    \\ Cases_on`loc` \\ gvs[assign_target_def]
    \\ gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
    \\ TRY(drule get_scopes_result \\ simp[])
    \\ TRY(drule lift_option_type_state \\ simp[])
    \\ TRY(drule get_immutables_state \\ simp[])
    \\ TRY(drule lift_sum_state \\ simp[])
    \\ TRY(drule lookup_global_state \\ simp[])
    \\ TRY(drule assign_result_state \\ simp[])
    \\ TRY(
      gvs[bind_def, CaseEq"prod",CaseEq"sum"]
      \\ TRY(drule lift_option_state \\ simp[])
      \\ pairarg_tac \\ gvs[bind_apply,CaseEq"prod",CaseEq"sum",ignore_bind_apply]
      \\ gvs[set_scopes_def, return_def]
      \\ TRY(drule lift_sum_state \\ simp[])
      \\ ntac 3 strip_tac \\ gvs[]
      \\ drule assign_result_state
      \\ strip_tac \\ gvs[]
      \\ suspend "replace")
    >- (
      rpt(disch_then strip_assume_tac) \\ gvs[]
      \\ funpow 2 drule_then irule set_immutable_well_typed
      \\ gvs[]
      \\ suspend "set_immutable" )
    \\ imp_res_tac set_immutable_error_state >- gvs[]
    \\ ntac 2 strip_tac
    \\ gvs[toplevel_value_CASE_rator, AllCaseEqs(), bind_apply, ignore_bind_apply]
    \\ TRY(drule lift_option_type_state \\ simp[])
    \\ TRY(drule lift_sum_state \\ simp[])
    \\ TRY(drule assign_result_state \\ simp[])
    \\ rpt (disch_then strip_assume_tac) \\ gvs[]
    \\ TRY(drule_all write_storage_slot_well_typed)
    \\ TRY(drule_all set_global_well_typed) \\ gvs[]
    >- (
      reverse $ gvs[prod_CASE_rator, bind_def, AllCaseEqs()]
      \\ TRY(drule lift_option_type_state \\ simp[])
      \\ pairarg_tac \\ strip_tac \\ gvs[]
      \\ reverse $ gvs[prod_CASE_rator, bind_def, AllCaseEqs()]
      \\ TRY(drule lift_option_type_state \\ simp[])
      \\ pairarg_tac \\ strip_tac \\ gvs[]
      \\ gvs[bind_apply, AllCaseEqs(), ignore_bind_apply]
      \\ imp_res_tac lift_option_type_state \\ gvs[]
      \\ TRY(drule lift_sum_state \\ simp[])
      \\ TRY(drule read_storage_slot_state \\ simp[])
      \\ TRY(drule assign_result_state \\ simp[])
      \\ rpt (disch_then strip_assume_tac) \\ gvs[]
      \\ TRY(drule_all write_storage_slot_well_typed)
      \\ simp[])
   \\ reverse $ gvs[bind_def, AllCaseEqs()]
   >- ( drule resolve_array_element_state \\ rw[] )
   \\ pairarg_tac
   \\ gvs[type_value_CASE_rator, AllCaseEqs(), bind_apply, ignore_bind_apply,
          bound_CASE_rator]
   \\ imp_res_tac read_storage_slot_state
   \\ imp_res_tac lift_sum_state
   \\ imp_res_tac resolve_array_element_state
   \\ imp_res_tac assign_result_state
   \\ gvs[]
   \\ imp_res_tac write_storage_slot_well_typed
   \\ gvs[])
 \\ conj_tac
 >- (
   rpt gen_tac \\ strip_tac
   \\ rpt gen_tac
   \\ simp[evaluate_def, bind_apply, return_def, AllCaseEqs()]
   \\ strip_tac \\ gvs[]
   \\ first_x_assum drule
   \\ gvs[well_typed_atarget_def, SF ETA_ss]
   \\ Cases_on`v` \\ gvs[assign_target_def, raise_def]
   \\ Cases_on`a` \\ gvs[assign_target_def, raise_def]
   \\ gvs[ignore_bind_apply, AllCaseEqs(), return_def,
          type_check_def, assert_def]
   \\ disch_then $ drule_then drule \\ gvs[]
   \\ gvs[evaluate_type_def, AllCaseEqs(), PULL_EXISTS]
   \\ gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF]
   \\ gvs[listTheory.LIST_REL_EL_EQN, listTheory.EVERY_EL]
   \\ disch_then irule
   \\ drule eval_targets_length
   \\ simp[] \\ strip_tac
   \\ rpt strip_tac
   \\ gvs[optionTheory.IS_SOME_EXISTS, listTheory.EL_MAP, PULL_EXISTS]
   \\ gvs[value_has_type_def,
          values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN]
   \\ gvs[listTheory.EL_MAP]
   \\ first_x_assum drule
   \\ first_x_assum drule
   \\ rw[] \\ gvs[])
 \\ conj_tac
 >- ( simp[evaluate_def, return_def, assign_target_def] )
 \\ rpt gen_tac \\ strip_tac
 \\ rpt gen_tac
 \\ simp_tac std_ss [evaluate_def, bind_apply, AllCaseEqs(), return_def]
 \\ strip_tac
 \\ rpt BasicProvers.VAR_EQ_TAC
 \\ first_x_assum drule
 \\ Cases_on`tys` \\ fs[]
 \\ disch_then drule
 \\ BasicProvers.VAR_EQ_TAC
 \\ reverse $ fs[assign_target_def, ignore_bind_apply, AllCaseEqs()]
 >- (
   rpt BasicProvers.VAR_EQ_TAC
   \\ first_x_assum $ funpow 2 drule_then drule
   \\ simp[] )
 \\ disch_then drule
 \\ gvs[]
 \\ disch_then irule
 \\ first_x_assum irule
 \\ rpt(goal_assum $ drule_at Any)
QED

Resume assign_target_well_typed[replace]:
  qmatch_asmsub_rename_tac`get_scopes st`
  \\ sg `lookup_scopes (string_to_num s) st.scopes = SOME (tv,a)`
  >- (
    gvs[get_scopes_def, return_def, lift_option_def, option_CASE_rator]
    >> gvs[AllCaseEqs(), return_def, raise_def]
    >> irule find_containing_scope_lookup
    >> goal_assum drule )
  \\ `loc_type cx st (ScopedVar s) tv` by rw[loc_type_def]
  \\ gvs[well_typed_atarget_def]
  \\ drule_all eval_base_target_type_connection
  \\ strip_tac \\ gvs[]
  \\ drule_at Any lookup_scopes_well_typed
  \\ impl_tac >- gvs[state_well_typed_def]
  \\ gvs[lift_sum_def, sum_CASE_rator, AllCaseEqs(), raise_def, return_def]
  \\ strip_tac
  \\ drule assign_subscripts_preserves_type
  \\ simp[] \\ strip_tac
  \\ gvs[lift_option_def, option_CASE_rator, AllCaseEqs(),
         return_def, raise_def]
  \\ conj_tac
  >- (
    irule state_well_typed_with_scopes
    \\ drule find_containing_scope_structure
    \\ strip_tac
    \\ gvs[state_well_typed_def]
    \\ gvs[scope_well_typed_def, FLOOKUP_UPDATE]
    \\ rw[] \\ rw[]
    \\ first_x_assum irule
    \\ goal_assum drule )
  \\ irule (iffRL $ cj 1 env_consistent_scopes_only)
  \\ gvs[env_consistent_def]
  \\ rw[]
  \\ TRY (
       first_x_assum irule
       \\ goal_assum drule \\ rw[])
  \\ drule find_containing_scope_structure
  \\ strip_tac \\ gvs[]
  \\ Cases_on`string_to_num s = id`
  >- (
    drule find_containing_scope_pre_none \\ strip_tac
    \\ drule lookup_scopes_update
    \\ strip_tac \\ gvs[]
    \\ first_x_assum (drule_then irule)
    \\ goal_assum drule )
  \\ drule lookup_scopes_update_other
  \\ strip_tac
  \\ first_x_assum(drule_then irule)
  \\ gvs[]
QED

Resume assign_target_well_typed[set_immutable]:
  (* Extract FLOOKUP from lift_option_type *)
  gvs[get_immutables_def, bind_apply, AllCaseEqs(), return_def]
  \\ gvs[lift_option_type_def, lift_sum_def,
         option_CASE_rator, sum_CASE_rator, AllCaseEqs(),
         return_def, raise_def]
  \\ gvs[lift_option_type_def, lift_sum_def,
         option_CASE_rator, sum_CASE_rator, AllCaseEqs(),
         return_def, raise_def,
         get_address_immutables_def, lift_option_def]
  \\ conj_tac
  (* Conjunct 1: ∃old_v. FLOOKUP ... = SOME (FST tva, old_v) *)
  >- (qexists_tac`SND tva` \\ Cases_on`tva` \\ gvs[])
  (* Conjunct 2: value_has_type (FST tva) a' *)
  \\ `loc_type cx s'³' (ImmutableVar s) (FST tva)` by
       (rw[loc_type_def, get_immutables_def, bind_apply, return_def,
           get_address_immutables_def, lift_option_def, option_CASE_rator]
        \\ qexists_tac`SND tva` \\ Cases_on`tva` \\ gvs[])
  \\ gvs[well_typed_atarget_def]
  \\ drule_all eval_base_target_type_connection
  \\ strip_tac \\ gvs[]
  (* Get value_has_type (FST tva) (SND tva) from imms_well_typed *)
  \\ sg `value_has_type (FST tva) (SND tva)`
  >- (
       gvs[state_well_typed_def, EVERY_MEM, FORALL_PROD] >>
       `imms_well_typed imms'` by
         (first_x_assum irule >>
          drule alistTheory.ALOOKUP_MEM >> strip_tac >>
          goal_assum drule) >>
       gvs[imms_well_typed_def, get_source_immutables_def] >>
       Cases_on`tva` >> gvs[] >>
       Cases_on`ALOOKUP imms' (current_module cx)` >> gvs[] >>
       first_x_assum irule >>
       goal_assum drule >> goal_assum drule)
  \\ drule assign_subscripts_preserves_type
  \\ simp[]
QED

Finalise assign_target_well_typed

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
  ho_match_mp_tac evaluate_ind
  (* P0: eval_stmt cases 0-14 — all trivial *)
  >> conj_tac >- simp[] (* Pass *)
  >> conj_tac >- simp[] (* Continue *)
  >> conj_tac >- simp[] (* Break *)
  >> conj_tac >- simp[] (* Return NONE *)
  >> conj_tac >- simp[] (* Return SOME *)
  >> conj_tac >- simp[] (* Raise *)
  >> conj_tac >- simp[] (* Assert *)
  >> conj_tac >- simp[] (* Log *)
  >> conj_tac >- simp[] (* AnnAssign *)
  >> conj_tac >- simp[] (* Append *)
  >> conj_tac >- simp[] (* Assign *)
  >> conj_tac >- simp[] (* AugAssign *)
  >> conj_tac >- simp[] (* If *)
  >> conj_tac >- simp[] (* For *)
  >> conj_tac >- simp[] (* Expr *)
  (* P1: eval_stmts 15-16 — trivial *)
  >> conj_tac >- simp[] (* [] *)
  >> conj_tac >- simp[] (* s::ss *)
  (* P2: eval_iterator 17-18 *)
  (* P2: eval_iterator *)
  >> conj_tac >- suspend "Array"
  >> conj_tac >- suspend "Range"
  (* P3: eval_target *)
  >> conj_tac >- suspend "BaseTarget"
  >> conj_tac >- suspend "TupleTarget"
  (* P4: eval_targets *)
  >> conj_tac >- suspend "targets_nil"
  >> conj_tac >- suspend "targets_cons"
  (* P5: eval_base_target *)
  >> conj_tac >- suspend "NameTarget"
  >> conj_tac >- suspend "BareGlobalNameTarget"
  >> conj_tac >- suspend "TopLevelNameTarget"
  >> conj_tac >- suspend "AttributeTarget"
  >> conj_tac >- suspend "SubscriptTarget"
  (* P6: eval_for — trivial *)
  >> conj_tac >- simp[]
  >> conj_tac >- simp[]
  (* P7: eval_expr *)
  >> conj_tac >- suspend "Name_nr"
  >> conj_tac >- suspend "BareGlobalName_nr"
  >> conj_tac >- suspend "TopLevelName_nr"
  >> conj_tac >- suspend "FlagMember_nr"
  >> conj_tac >- suspend "IfExp_nr"
  >> conj_tac >- suspend "Literal_nr"
  >> conj_tac >- suspend "StructLit_nr"
  >> conj_tac >- suspend "Subscript_nr"
  >> conj_tac >- suspend "Attribute_nr"
  >> conj_tac >- suspend "Builtin_nr"
  >> conj_tac >- suspend "Pop_nr"
  >> conj_tac >- suspend "TypeBuiltin_nr"
  >> conj_tac >- suspend "Send_nr"
  >> conj_tac >- suspend "ExtCall_nr"
  >> conj_tac >- suspend "IntCall_nr"
  (* P8: eval_exprs *)
  >> conj_tac >- suspend "exprs_nil_nr"
  >> suspend "exprs_cons_nr"
QED

(* --- Resume blocks for evaluate_no_return --- *)

(* Most cases follow the same pattern: unfold, use error lemmas + IH *)
val enr_tac =
  rw[Once evaluate_def, bind_apply, AllCaseEqs(),
     return_def, raise_def, ignore_bind_apply,
     get_scopes_def, type_check_def, assert_def,
     get_address_immutables_def, check_def,
     option_CASE_rator, sum_CASE_rator]
  >> TRY (first_x_assum drule >> rw[])
  >> TRY (drule lift_option_type_error >> rw[])
  >> TRY (drule lift_option_error >> rw[])
  >> TRY (drule lift_sum_error >> rw[])
  >> TRY (drule assign_target_no_return >> rw[])
  >> TRY (drule assign_result_error >> rw[])
  >> TRY (drule read_storage_slot_error >> rw[])
  >> TRY (drule write_storage_slot_error >> rw[])
  >> TRY (drule set_global_error >> rw[])
  >> TRY (drule lookup_global_error >> rw[])
  >> TRY (drule get_immutables_error >> rw[])
  >> TRY (drule materialise_error >> rw[])
  >> TRY (drule get_Value_error >> rw[])
  >> TRY (drule lookup_flag_mem_error >> rw[])
  >> TRY (drule check_array_bounds_error >> rw[])
  >> TRY (drule toplevel_array_length_error >> rw[])
  >> TRY (drule switch_BoolV_error >> simp[] >> rw[])

Resume evaluate_no_return[Array]:
  enr_tac
QED

Resume evaluate_no_return[Range]:
  enr_tac
  >> first_x_assum drule_all \\ rw[]
QED

Resume evaluate_no_return[BaseTarget]:
  enr_tac
  >> gvs[bind_def, AllCaseEqs(), prod_CASE_rator]
  >> TRY pairarg_tac \\ gvs[return_def]
  >> first_x_assum drule_all \\ rw[]
QED

Resume evaluate_no_return[TupleTarget]:
  enr_tac
QED

Resume evaluate_no_return[targets_nil]: enr_tac
QED

Resume evaluate_no_return[targets_cons]:
  enr_tac
  >> first_x_assum drule_all \\ rw[]
QED

Resume evaluate_no_return[NameTarget]:
  enr_tac
QED

Resume evaluate_no_return[BareGlobalNameTarget]: enr_tac
QED

Resume evaluate_no_return[TopLevelNameTarget]: enr_tac
QED

Resume evaluate_no_return[AttributeTarget]:
  enr_tac
  >> gvs[bind_def, AllCaseEqs(), prod_CASE_rator]
  >> TRY pairarg_tac \\ gvs[return_def]
  >> first_x_assum drule_all \\ rw[]
QED

Resume evaluate_no_return[SubscriptTarget]:
  enr_tac
  >> gvs[bind_def, AllCaseEqs(), prod_CASE_rator]
  >> TRY pairarg_tac \\ gvs[return_def]
  >> pop_assum mp_tac \\ enr_tac
  >> first_x_assum drule_all \\ rw[]
QED

Resume evaluate_no_return[Name_nr]: enr_tac
QED

Resume evaluate_no_return[BareGlobalName_nr]: enr_tac
QED

Resume evaluate_no_return[TopLevelName_nr]:
  enr_tac \\ strip_tac \\ enr_tac
QED

Resume evaluate_no_return[FlagMember_nr]:
  enr_tac
  >> strip_tac >> gvs[]
  >> drule lookup_flag_mem_error >> rw[]
QED

Resume evaluate_no_return[IfExp_nr]:
  enr_tac
  \\ strip_tac \\ enr_tac
  \\ TRY(first_x_assum drule_all)
  \\ rw[]
  \\ goal_assum $ drule_at Any
QED

Resume evaluate_no_return[Literal_nr]: enr_tac
QED

Resume evaluate_no_return[StructLit_nr]: enr_tac
QED

Resume evaluate_no_return[Subscript_nr]:
  enr_tac
  \\ first_x_assum drule_all \\ rw[]
  \\ gvs[bind_def, AllCaseEqs(), prod_CASE_rator, return_def]
  \\ enr_tac
QED

Resume evaluate_no_return[Attribute_nr]: enr_tac
QED

Resume evaluate_no_return[Builtin_nr]:
  enr_tac \\ strip_tac \\ gvs[]
QED

Resume evaluate_no_return[Pop_nr]:
  enr_tac
  >> gvs[bind_def, AllCaseEqs(), prod_CASE_rator]
  >> TRY pairarg_tac \\ gvs[return_def]
  >> pop_assum mp_tac \\ enr_tac
  \\ strip_tac
  \\ drule $ cj 1 assign_target_no_return
  \\ rw[]
QED

Resume evaluate_no_return[TypeBuiltin_nr]:
  enr_tac \\ strip_tac \\ gvs[]
QED

Resume evaluate_no_return[Send_nr]:
  enr_tac \\ strip_tac \\ gvs[]
  \\ drule transfer_value_error \\ rw[]
QED

Resume evaluate_no_return[ExtCall_nr]:
  enr_tac
  \\ gvs[bind_def, COND_RATOR, return_def, AllCaseEqs()]
  \\ strip_tac \\ gvs[get_transient_storage_def, return_def] \\ enr_tac
  \\ TRY pairarg_tac \\ gvs[]
  \\ pop_assum mp_tac \\ enr_tac
  \\ gvs[update_transient_def, update_accounts_def,
         get_transient_storage_def, return_def]
  >- (goal_assum drule_all)
  \\ gvs[lift_sum_runtime_def, CaseEq"sum", return_def, raise_def,
         sum_CASE_rator]
  \\ pairarg_tac
  \\ gvs[ignore_bind_apply, AllCaseEqs(), bind_apply,
         assert_def, return_def]
  \\ pop_assum mp_tac \\ enr_tac
  \\ rpt(goal_assum $ drule_at Any)
  \\ gvs[update_transient_def, update_accounts_def, return_def]
QED

(* TODO: move *)
Theorem exception_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="exception"}));

Resume evaluate_no_return[IntCall_nr]:
  enr_tac \\ strip_tac \\ gvs[]
  \\ gvs[finally_def, AllCaseEqs(), ignore_bind_apply, return_def,
         pop_function_def, set_scopes_def, raise_def, try_def,
         push_function_def]
  \\ gvs[oneline handle_function_def, AllCaseEqs(),
         exception_CASE_rator, return_def, raise_def]
  \\ first_x_assum drule_all \\ rw[]
QED

Resume evaluate_no_return[exprs_nil_nr]: enr_tac
QED

Resume evaluate_no_return[exprs_cons_nr]:
  enr_tac \\ strip_tac \\ gvs[]
  \\ first_x_assum drule_all \\ rw[]
QED

Finalise evaluate_no_return

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
  (!cx it. !env st res st'.
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P3: eval_target *)
  (!cx g. !env st res st'.
    (?ty. well_typed_atarget env g ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_target cx g st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P4: eval_targets *)
  (!cx gs. !env st res st'.
    EVERY (\g. ?ty. well_typed_atarget env g ty) gs /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_targets cx gs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P5: eval_base_target *)
  (!cx bt. !env st res st'.
    (?ty. well_typed_target env bt ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st') /\
  (* P6: eval_for *)
  (* P6: eval_for — env is the OUTER env (without loop var),
     body is typed under env |+ (nm, typ) *)
  (!cx tyv nm body vs. !env typ ret_ty st res st'.
    well_typed_stmts (env with var_types updated_by (flip FUPDATE (nm, typ)))
                     ret_ty body /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    nm NOTIN FDOM env.var_types /\
    eval_for cx tyv nm body vs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    !v ret_tv. res = INR (ReturnException v) /\
               evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
               value_has_type ret_tv v) /\
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
          (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv v)))) /\
  (* P8: eval_exprs — covers both success and failure *)
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!vs. res = INL vs ==>
      LIST_REL (\v e. ?tyv.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
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
  (* 4: Return SOME *)   >- suspend "ReturnSome"
  (* 5: Raise *)         >- suspend "Raise"
  (* 6: Assert *)        >- suspend "Assert"
  (* 7: Log *)           >- suspend "Log"
  (* 8: AnnAssign *)     >- suspend "AnnAssign"
  (* 9: Append *)        >- suspend "Append"
  (* 10: Assign *)       >- suspend "assign"
  (* 11: AugAssign *)    >- suspend "AugAssign"
  (* 12: If *)           >- suspend "If"
  (* 13: For *)          >- suspend "For"
  (* 14: Expr *)         >- suspend "Expr"
  (* ===== P1: eval_stmts (goals 15-16) ===== *)
  (* 15: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 16: s::ss — sequential: eval_stmt s then eval_stmts ss *)
  >- (rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, ignore_bind_apply] >>
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
  (* 17: Array *)        >- suspend "Array"
  (* 18: Range *)        >- suspend "Range"
  (* ===== P3: eval_target (goals 19-20) ===== *)
  (* 19: BaseTarget *)   >- suspend "BaseTarget"
  (* 20: TupleTarget *)  >- suspend "TupleTarget"
  (* ===== P4: eval_targets (goals 21-22) ===== *)
  (* 21: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 22: g::gs *)        >- suspend "targets_cons"
  (* ===== P5: eval_base_target (goals 23-27) ===== *)
  (* 23: NameTarget *)        >- suspend "NameTarget"
  (* 24: BareGlobalNameTarget *) >- suspend "BareGlobalNameTarget"
  (* 25: TopLevelNameTarget *) >- suspend "TopLevelNameTarget"
  (* 26: AttributeTarget *)   >- suspend "AttributeTarget"
  (* 27: SubscriptTarget *)   >- suspend "SubscriptTarget"
  (* ===== P6: eval_for (goals 28-29) ===== *)
  (* 28: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 29: v::vs *)        >- suspend"cons"
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
  (* 31: BareGlobalName *) >- suspend "BareGlobalName"
  (* 32: TopLevelName *)   >- suspend "TopLevelName"
  (* 33: FlagMember *)     >- suspend "FlagMember"
  (* 34: IfExp *)          >- suspend "IfExp"
  (* 35: Literal *)        >- suspend "Literal"
  (* 36: StructLit *)      >- suspend "StructLit"
  (* 37: Subscript *)      >- suspend"Subscript"
  (* 38: Attribute *)      >- suspend"Attribute"
  (* 39: Builtin *)        >- suspend "Builtin"
  (* 40: Pop *)            >- suspend "Pop"
  (* 41: TypeBuiltin *)    >- suspend "TypeBuiltin"
  (* 42: Call Send *)      >- suspend"Send"
  (* 43: Call ExtCall *)   >- suspend"ExtCall"
  (* 44: Call IntCall *)   >- suspend"IntCall"
  (* ===== P8: eval_exprs (goals 45-46) ===== *)
  (* 45: [] *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, return_def])
  (* 46: e::es *)
  >- suspend "P8cons"
QED

Resume type_preservation[cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum`eval_for _ _ _ _ (_::_) _ = _`mp_tac >>
  rewrite_tac[evaluate_def] >>
  rewrite_tac[bind_apply, ignore_bind_apply, CaseEq"sum", CaseEq"prod"] >>
  simp_tac std_ss [] >> strip_tac >>
  pop_assum mp_tac >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (
    strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
    \\ simp_tac std_ss []
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [push_scope_with_var_def, return_def] )
  \\ first_x_assum $ drule_then drule
  \\ strip_tac
  \\ simp_tac std_ss [bind_apply]
  \\ CASE_TAC
  \\ reverse CASE_TAC
  >- (
    strip_tac \\ rpt BasicProvers.VAR_EQ_TAC >>
    last_x_assum(qspec_then`ARB`kall_tac) >>
    gvs[finally_def,ignore_bind_apply,bind_apply,
        return_def,pop_scope_def,raise_def,try_def,
        push_scope_with_var_def] >>
    pop_assum mp_tac >> CASE_TAC >>
    first_x_assum $ drule_at Any >>
    impl_tac >- (
      gvs[push_scope_with_var_def, return_def,
          state_well_typed_def, scope_well_typed_def,
          FLOOKUP_UPDATE, env_consistent_def,
          lookup_scopes_def] >>
      conj_tac >> rpt gen_tac >>
      Cases_on`nm = id` >> strip_tac \\ gvs[] >>
      first_x_assum (drule_then irule) >>
      goal_assum drule) >>
    strip_tac >>
    CASE_TAC >> gvs[]
    >- ( simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
         gvs[env_consistent_def, lookup_scopes_def] >>
         first_x_assum MATCH_ACCEPT_TAC )
    >> simp[handle_loop_exception_def] >>
    simp[AllCaseEqs()] >>
    simp[COND_RATOR, return_def, raise_def] >>
    strip_tac >> gvs[CaseEq"bool"] >>
    TRY (gvs[env_consistent_def, lookup_scopes_def]
         \\ first_x_assum MATCH_ACCEPT_TAC) >>
    conj_tac >- gvs[state_well_typed_def] >>
    `r' with scopes := tl = r' with scopes := TL r'.scopes` by gvs[] >>
    pop_assum SUBST_ALL_TAC >>
    irule env_consistent_pop_scope >>
    simp[] >>
    goal_assum $ drule_at Any >>
    rw[] >>
    drule eval_stmts_new_in_head_not_in_tail >>
    simp[push_scope_with_var_def, return_def, FDOM_FUPDATE] ) >>
  last_x_assum $ drule_then drule >>
  strip_tac >>
  IF_CASES_TAC >- (
    gvs[return_def] >>
    strip_tac >> gvs[] >>
    gvs[finally_def, try_def, AllCaseEqs(), bind_apply,
        ignore_bind_apply, return_def, pop_scope_def, raise_def] >>
    gvs[handle_loop_exception_def, return_def, raise_def, AllCaseEqs()] >>
    gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
    first_x_assum $ drule_at Any >>
    impl_tac >- (
      gvs[push_scope_with_var_def, return_def,
          state_well_typed_def, scope_well_typed_def,
          FLOOKUP_UPDATE, env_consistent_def,
          lookup_scopes_def] >>
      conj_tac >> rpt gen_tac >>
      Cases_on `nm = id` >> strip_tac >> gvs[] >>
      first_x_assum (drule_then irule) >>
      goal_assum drule) >>
    strip_tac >>
    conj_tac >- gvs[state_well_typed_def] >>
    `s'' with scopes := tl = s'' with scopes := TL s''.scopes` by gvs[] >>
    pop_assum SUBST_ALL_TAC >>
    irule env_consistent_pop_scope >> simp[] >>
    goal_assum $ drule_at Any >> rw[] >>
    drule eval_stmts_new_in_head_not_in_tail >>
    simp[push_scope_with_var_def, return_def, FDOM_FUPDATE] >>
    strip_tac >> first_x_assum irule >>
    gvs[push_scope_with_var_def, return_def, FDOM_FUPDATE] ) >>
  strip_tac >>
  first_x_assum $ drule_at(Pat`eval_for`) >>
  gvs[] >>
  disch_then (qspecl_then [`env`, `typ`, `ret_ty`] mp_tac) >>
  simp[] >>
  disch_then irule >>
  (* Need: env_consistent env cx r ∧ state_well_typed r *)
  (* r comes from finally (try body handle_loop_exception) pop_scope y = (INL F, r) *)
  (* Same push/pop argument as broke=T case *)
  (* First apply IH_body to get state after body, then pop_scope *)
  gvs[finally_def, try_def, AllCaseEqs(), bind_apply,
      ignore_bind_apply, return_def, pop_scope_def, raise_def] >>
  gvs[handle_loop_exception_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  first_x_assum $ drule_at Any >>
  (impl_tac >- (
    gvs[push_scope_with_var_def, return_def,
        state_well_typed_def, scope_well_typed_def,
        FLOOKUP_UPDATE, env_consistent_def,
        lookup_scopes_def] >>
    conj_tac >> rpt gen_tac >>
    Cases_on `nm = id` >> strip_tac >> gvs[] >>
    first_x_assum (drule_then irule) >>
    goal_assum drule)) >>
  strip_tac >>
  (conj_tac >- gvs[state_well_typed_def]) >>
  `s'' with scopes := tl = s'' with scopes := TL s''.scopes` by gvs[] >>
  pop_assum SUBST_ALL_TAC >>
  irule env_consistent_pop_scope >> simp[] >>
  goal_assum $ drule_at Any >> rw[] >>
  drule eval_stmts_new_in_head_not_in_tail >>
  simp[push_scope_with_var_def, return_def, FDOM_FUPDATE] >>
  strip_tac >> first_x_assum irule >>
  gvs[push_scope_with_var_def, return_def, FDOM_FUPDATE]
QED

Resume type_preservation[Send]:
  cheat
QED

Resume type_preservation[ExtCall]:
  cheat
QED

Resume type_preservation[IntCall]:
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [well_typed_expr_def] >>
  rpt gen_tac >> strip_tac >>
  (* Unfold eval_expr for IntCall *)
  qpat_x_assum `eval_expr _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, AllCaseEqs(),
                   PULL_EXISTS] >>
  rpt gen_tac >>
  reverse(disch_then strip_assume_tac)
  (* Error cases from first batch of checks *)
  >- (
    rpt(first_x_assum(qspec_then`ARB`kall_tac))
    \\ gvs[check_def, assert_def] )
  >- (
    rpt(first_x_assum(qspec_then`ARB`kall_tac))
    \\ imp_res_tac lift_option_type_state
    \\ gvs[check_def, assert_def] )
  >- (
    rpt(first_x_assum(qspec_then`ARB`kall_tac))
    \\ imp_res_tac lift_option_type_state
    \\ gvs[check_def, assert_def]) >>
  (* LET bindings for destructuring fn_info *)
  qmatch_goalsub_abbrev_tac`P` >>
  qpat_x_assum`LET _ _ _ = _` mp_tac >>
  BasicProvers.LET_ELIM_TAC >>
  qunabbrev_tac`P` >>
  (* Continue decomposing *)
  qpat_x_assum`_ = (res,_)`mp_tac >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, AllCaseEqs(),
                   PULL_EXISTS] >>
  rpt gen_tac >>
  reverse(disch_then strip_assume_tac)
  (* Error from type_check or eval_exprs args *)
  >- (
    rpt(first_x_assum(qspec_then`ARB`kall_tac))
    \\ imp_res_tac lift_option_type_state
    \\ imp_res_tac type_check_state
    \\ gvs[check_def, assert_def] )
  >- (
    (* eval_exprs cx es failed — use IH_args for state_well_typed + env_consistent *)
    first_x_assum $ drule_at(Pat`eval_exprs`) >>
    rpt(first_x_assum(qspec_then`ARB`kall_tac))
    \\ imp_res_tac lift_option_type_state
    \\ imp_res_tac type_check_state
    \\ gvs[check_def, assert_def]
    \\ disch_then irule \\ rw[]
    \\ goal_assum drule
    \\ goal_assum (drule_at Any)
    \\ gvs[]
    \\ goal_assum drule ) >>
  (* eval_exprs cx es succeeded — continue *)
  qmatch_goalsub_abbrev_tac`P` >>
  qpat_x_assum`LET _ _ _ = _` mp_tac >>
  BasicProvers.LET_ELIM_TAC >>
  qunabbrev_tac`P` >>
  qpat_x_assum`_ = (res,_)`mp_tac >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, AllCaseEqs(),
                   PULL_EXISTS] >>
  rpt gen_tac >>
  reverse(disch_then strip_assume_tac)
  >- (
    (* eval_exprs cxd needed_dflts failed *)
    (* Use IH_args for env_consistent env cx after args eval *)
    first_x_assum $ drule_at(Pat`eval_exprs`) >>
    first_x_assum $ drule_at(Pat`eval_exprs`) >>
    rpt(first_x_assum(qspec_then`ARB`kall_tac))
    \\ imp_res_tac lift_option_type_state
    \\ imp_res_tac type_check_state
    \\ gvs[check_def, assert_def]
    \\ disch_then drule
    \\ gvs[] \\ strip_tac
    \\ disch_then drule
    \\ disch_then drule
    \\ gvs[]
    \\ disch_then drule_all
    \\ strip_tac
    \\ first_x_assum drule
    \\ gvs[]
    \\ disch_then drule
    \\ disch_then drule
    \\ cheat ) >>
  cheat
QED

Resume type_preservation[For]:
  cheat
QED

Resume type_preservation[Attribute]:
  cheat
QED

(* Helper: subscript_type_ok preserves evaluate_type success *)
Theorem subscript_type_ok_evaluate:
  !ct it rt tenv atv.
    subscript_type_ok ct it rt /\
    evaluate_type tenv ct = SOME atv ==>
    ?rtv. evaluate_type tenv rt = SOME rtv
Proof
  Cases >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
  gvs[EVERY_MEM] >>
  first_x_assum (qspec_then `evaluate_type tenv rt` mp_tac) >>
  simp[MEM_MAP] >> impl_tac >- (qexists_tac `rt` >> simp[]) >>
  simp[IS_SOME_EXISTS]
QED

(* Helper: array_index on a well-typed array returns a well-typed element *)
Theorem array_index_well_typed:
  !elem_tv bound av i v.
    value_has_type (ArrayTV elem_tv bound) (ArrayV av) /\
    well_formed_type_value elem_tv /\
    array_index (ArrayTV elem_tv bound) av i = SOME v ==>
    value_has_type elem_tv v
Proof
  rpt gen_tac >> Cases_on`av` >>
  simp[array_index_def, value_has_type_inv] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  TRY (drule_all oEL_all_have_type >> simp[] >> NO_TAC) >>
  TRY (irule default_value_well_typed >> simp[] >> NO_TAC) >>
  imp_res_tac sparse_has_type_all_have_type >>
  gvs[all_have_type_EVERY, EVERY_MEM] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  first_x_assum $ qspec_then`v`mp_tac >>
  simp[MEM_MAP] >> disch_then irule >>
  qexists_tac`(Num i, v)` >> simp[]
QED

(* Helper: decode_value always produces a well-typed value *)
Theorem decode_value_well_typed:
  (!storage offset tv v.
     decode_value storage offset tv = SOME v ==> value_has_type tv v) /\
  (!storage offset tvs vs.
     decode_tuple storage offset tvs = SOME vs ==> values_have_types tvs vs) /\
  (!storage offset tv n vs.
     decode_static_array storage offset tv n = SOME vs ==> all_have_type tv vs) /\
  (!storage offset tv n vs.
     decode_dyn_array storage offset tv n = SOME vs ==> all_have_type tv vs) /\
  (!storage offset ftypes fields.
     decode_struct storage offset ftypes = SOME fields ==>
     struct_has_type ftypes fields)
Proof
  cheat
QED

(* Helper: read_storage_slot returns a well-typed value *)
Theorem read_storage_slot_well_typed:
  !cx is_transient slot tv st v st'.
    read_storage_slot cx is_transient slot tv st = (INL v, st') ==>
    value_has_type tv v
Proof
  simp[read_storage_slot_def, bind_apply, AllCaseEqs(),
       get_storage_backend_def, return_def, lift_option_def,
       option_CASE_rator, raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule (cj 1 decode_value_well_typed) >>
  goal_assum drule
QED

Resume type_preservation[Subscript]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum`well_typed_expr _ (Subscript _ _ _)`mp_tac >>
  rewrite_tac[well_typed_expr_def] >> strip_tac >>
  qpat_x_assum`eval_expr _ (Subscript _ _ _) _ = _`mp_tac >>
  rewrite_tac[evaluate_def] >>
  rewrite_tac[bind_def, ignore_bind_def, CaseEq"sum", CaseEq"prod"] >>
  simp_tac std_ss [] >>
  strip_tac >>
  (* Apply IH_e: state preservation through eval_expr e *)
  first_x_assum $ funpow 4 drule_then drule >>
  strip_tac >>
  (* Case split on eval_expr e result *)
  reverse(Cases_on`x`) >- (last_x_assum kall_tac >> gvs[])
  (* Apply IH_e': state preservation through eval_expr e' *)
  >> first_x_assum drule
  >> disch_then $ funpow 3 drule_then drule
  >> gvs[bind_apply, AllCaseEqs(), sum_CASE_rator,
         prod_CASE_rator, return_def, raise_def]
  >> imp_res_tac lift_sum_state
  >> imp_res_tac lift_option_state
  >> imp_res_tac read_storage_slot_state
  >> imp_res_tac check_array_bounds_state
  >> imp_res_tac lift_option_type_state
  >> imp_res_tac get_Value_state
  >> gvs[expr_type_def, materialise_def, return_def]
  >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> imp_res_tac materialise_state >> gvs[]
  >> cheat
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
  \\ first_x_assum $ drule_at Any
  \\ simp_tac std_ss [PULL_EXISTS]
  \\ disch_then drule_all
  \\ strip_tac
  \\ qpat_x_assum`_ = (res,_)`mp_tac
  \\ simp_tac std_ss [sum_CASE_rator, CaseEq"sum", CaseEq"prod"]
  \\ reverse strip_tac
  >- (
    first_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[] \\ rw[]
    \\ imp_res_tac evaluate_no_return
    \\ gvs[] )
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [bind_apply, return_def]
  \\ CASE_TAC
  \\ BasicProvers.VAR_EQ_TAC
  \\ first_x_assum drule
  \\ disch_then $ funpow 4 drule_then drule
  \\ strip_tac
  \\ reverse CASE_TAC
  >- ( rw[] \\ drule (cj 8 evaluate_no_return) \\ rw[] )
  \\ CASE_TAC \\ gvs[]
  \\ reverse CASE_TAC
  >- ( drule materialise_error
       \\ drule materialise_state \\ rw[]  \\ gvs[] )
  \\ CASE_TAC
  \\ strip_tac \\ gvs[]
  \\ funpow 2 drule_then drule (cj 1 assign_target_well_typed)
  \\ strip_tac
  \\ qmatch_asmsub_rename_tac`assign_target _ _ _ _ = (_,atr)`
  \\ qmatch_asmsub_rename_tac`_ = (res,stf)`
  \\ `stf = atr` by gvs[CaseEq"sum"] \\ gvs[]
  \\ rw[] \\ gvs[CaseEq"sum"]
  \\ imp_res_tac assign_target_no_return
  \\ gvs[]
QED

(* ===== P0 cases ===== *)
Resume type_preservation[ReturnSome]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_stmt_def] >>
  qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
  rewrite_tac[evaluate_def] >>
  rewrite_tac[bind_def, CaseEq"sum", CaseEq"prod"] >>
  simp_tac std_ss [] >> strip_tac >>
  first_x_assum $ funpow 3 drule_then drule >> strip_tac >>
  gvs[bind_apply, AllCaseEqs(), return_def, raise_def,
      materialise_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac materialise_error >> gvs[] >>
  drule (cj 8 evaluate_no_return) >> gvs[]
QED
(* Common pattern for simple stmt cases:
   1. Strip, unfold well_typed_stmt and eval_stmt
   2. Decompose monadic chain with rewrite_tac
   3. Apply IH on sub-expressions via funpow N drule_then drule
   4. gvs to decompose remaining, imp_res_tac for state lemmas
   5. drule evaluate_no_return for ReturnException contradiction *)
Resume type_preservation[Raise]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_stmt_def] >>
  qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
  rewrite_tac[evaluate_def] >>
  rewrite_tac[bind_def, ignore_bind_def, CaseEq"sum", CaseEq"prod"] >>
  simp_tac std_ss [] >> strip_tac >>
  first_x_assum $ funpow 3 drule_then drule >> strip_tac >>
  gvs[bind_apply, AllCaseEqs(), return_def, raise_def,
      lift_option_type_def, option_CASE_rator] >>
  imp_res_tac get_Value_state >> gvs[] >>
  TRY (drule get_Value_error >> rw[] >> NO_TAC) >>
  drule (cj 8 evaluate_no_return) >> gvs[]
QED

Resume type_preservation[Assert]:
  cheat
QED

Resume type_preservation[Log]:
  cheat
QED

Resume type_preservation[AnnAssign]:
  cheat
QED

Resume type_preservation[Append]:
  cheat
QED

Resume type_preservation[AugAssign]:
  cheat
QED

Resume type_preservation[If]:
  cheat
QED

Resume type_preservation[Expr]:
  cheat
QED

(* ===== P2 cases ===== *)
Resume type_preservation[Array]:
  cheat
QED
Resume type_preservation[Range]:
  cheat
QED

(* ===== P3/P4 cases ===== *)
Resume type_preservation[BaseTarget]:
  cheat
QED
Resume type_preservation[TupleTarget]:
  cheat
QED
Resume type_preservation[targets_cons]:
  cheat
QED

(* ===== P5 cases ===== *)
Resume type_preservation[NameTarget]:
  cheat
QED
Resume type_preservation[BareGlobalNameTarget]:
  cheat
QED
Resume type_preservation[TopLevelNameTarget]:
  cheat
QED
Resume type_preservation[AttributeTarget]:
  cheat
QED
Resume type_preservation[SubscriptTarget]:
  cheat
QED

(* ===== P7 cases ===== *)
Resume type_preservation[BareGlobalName]:
  cheat
QED
Resume type_preservation[TopLevelName]:
  cheat
QED
Resume type_preservation[FlagMember]:
  cheat
QED
Resume type_preservation[IfExp]:
  cheat
QED
Resume type_preservation[Literal]:
  cheat
QED
Resume type_preservation[StructLit]:
  cheat
QED
Resume type_preservation[Builtin]:
  cheat
QED
Resume type_preservation[Pop]:
  cheat
QED
Resume type_preservation[TypeBuiltin]:
  cheat
QED

Finalise type_preservation
