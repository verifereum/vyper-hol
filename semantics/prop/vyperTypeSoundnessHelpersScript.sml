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
 *   IntCall                     : internal call type preservation (6 sub-proofs)
 *   set_immutable_well_typed    : set_immutable preserves state_well_typed + env_consistent
 *   set_global_well_typed       : set_global preserves state_well_typed + env_consistent
 *   write_storage_slot_well_typed : storage writes preserve state_well_typed + env_consistent
 *   (uses value_has_type from vyperTypingTheory for value/type compatibility)
 *   (uses assign_subscripts_preserves_type from vyperAssignPreservesTypeTheory)
 *
 * PROOF STATUS:
 *   type_preservation: 33 Resume blocks still cheated (out of 47 total).
 *     Proved inline: Pass, Continue, Break, Return NONE,
 *                    eval_stmts nil/cons, eval_targets nil, eval_for nil,
 *                    eval_exprs nil, Name
 *     Proved via Resume: ReturnSome, Raise1/2/3, IntCall (6 sub-proofs),
 *                        eval_for cons, P8cons (eval_exprs cons), assign
 *     Partial (trailing cheat): Subscript
 *
 * REMAINING CHEATS (33 Resume blocks + 1 helper, ordered by risk):
 *
 * --- HIGHEST RISK: evaluate_builtin type preservation ---
 *   39: Builtin — ~43 cases of evaluate_builtin, needs per-builtin
 *       value_has_type lemma. System builtins (RawCall, RawLog, etc.) have
 *       permissive typing (well_typed_builtin_app = T) — fundamental gap.
 *   41: TypeBuiltin — evaluate_type_builtin (Empty, Convert, AbiDecode, etc.)
 *
 * --- HIGH RISK: external calls ---
 *   43: Call ExtCall — needs evaluate_abi_decode_return to produce well-typed
 *       values (ABI decode correctness)
 *   42: Call Send — transfer_value state preservation
 *
 * --- MEDIUM RISK: decode/subscript/attribute ---
 *   decode_value_well_typed (helper) — mutual induction over 5 decode fns,
 *       currently cheated, used only by read_storage_slot_well_typed (unused)
 *   37: Subscript — partial proof, trailing cheat needs value_has_type for
 *       result after array index or storage read
 *   38: Attribute — attribute access typing
 *   36: StructLit — struct type evaluation
 *
 * --- MEDIUM RISK: control flow ---
 *   13: For — eval_iterator + scope manipulation
 *   40: Pop — array pop typing
 *
 * --- LOW RISK: simple stmt cases (follow Raise/ReturnSome pattern) ---
 *   6: Assert1/2/3, 7: Log, 8: AnnAssign, 9: Append,
 *   11: AugAssign, 12: If, 14: Expr
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

Theory vyperTypeSoundnessHelpers
Ancestors
  vyperTypeSoundnessDefs
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

(* ===== Type Classification Helpers ===== *)


(* Helper: looking up a variable in well-typed scopes gives a well-typed value *)
Theorem lookup_scopes_well_typed:
  !scopes id entry.
    EVERY scope_well_typed scopes /\
    lookup_scopes id scopes = SOME entry ==>
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  Induct >> simp[lookup_scopes_def] >>
  rpt gen_tac >>
  Cases_on `FLOOKUP h id` >> fs[] >>
  strip_tac >> fs[scope_well_typed_def] >>
  res_tac >> simp[]
QED

(* Helper: lookup_scopes_val returns a value that satisfies some type_value *)
Theorem lookup_scopes_val_well_typed:
  !scopes id v.
    EVERY scope_well_typed scopes /\
    lookup_scopes_val id scopes = SOME v ==>
    ?entry. lookup_scopes id scopes = SOME entry /\
            entry.value = v /\ value_has_type entry.type v
Proof
  Induct >> simp[lookup_scopes_def, lookup_scopes_val_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP h id` >> gvs[] >>
  fs[scope_well_typed_def] >> res_tac
QED

(* Helper: ALOOKUP into well-typed immutables list gives imms_well_typed *)
Theorem state_well_typed_imms_lookup[local]:
  !st addr mods.
    state_well_typed st /\
    ALOOKUP st.immutables addr = SOME mods ==>
    imms_well_typed mods
Proof
  rw[state_well_typed_def] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  fs[EVERY_MEM, FORALL_PROD] >>
  first_x_assum drule >> simp[]
QED

(* Helper: FLOOKUP into get_source_immutables of well-typed imms gives
   well_formed_type_value and value_has_type *)
Theorem imms_well_typed_src_lookup[local]:
  !mods src n tv v.
    imms_well_typed mods /\
    FLOOKUP (get_source_immutables src mods) n = SOME (tv, v) ==>
    value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[get_source_immutables_def] >>
  Cases_on `ALOOKUP mods src` >> gvs[] >>
  fs[imms_well_typed_def] >>
  first_x_assum (drule_all_then strip_assume_tac)
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

(* Phase 2: Operation-level helpers
 * Done: evaluate_literal_has_type, evaluate_builtin_bop_add_uint
 * TODO: general evaluate_builtin type preservation (all ~43 cases) *)

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
    bounded_int_op (Unsigned k) r = INL v ==>
    value_has_type (BaseTV (UintT k)) v
Proof
  rw[bounded_int_op_def] >>
  gvs[value_has_type_def, within_int_bound_def]
QED

Theorem bounded_int_op_signed:
  !k r v.
    bounded_int_op (Signed k) r = INL v ==>
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

(* Combined args + defaults typing: if args are well-typed (LIST_REL with vs)
   and defaults are well-typed (LIST_REL with dflt_vs), and their expr_types
   align with the parameter types, then all elements of vs ++ dflt_vs
   satisfy the corresponding parameter types. *)
Theorem args_dflts_typing_to_el:
  !tenv (params: (string # type) list) args vs dflt_vs needed_dflts.
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) vs args /\
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) dflt_vs needed_dflts /\
    MAP expr_type args = TAKE (LENGTH args) (MAP SND params) /\
    MAP expr_type needed_dflts =
      MAP SND (DROP (LENGTH args) params) /\
    LENGTH args + LENGTH needed_dflts = LENGTH params ==>
    !i tv. i < LENGTH params /\ i < LENGTH (vs ++ dflt_vs) /\
           evaluate_type tenv (SND (EL i params)) = SOME tv ==>
           value_has_type tv (EL i (vs ++ dflt_vs))
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `LENGTH vs = LENGTH args` by
    (qpat_x_assum `LIST_REL _ vs args` mp_tac >>
     simp[listTheory.LIST_REL_EL_EQN]) >>
  `LENGTH dflt_vs = LENGTH needed_dflts` by
    (qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
     simp[listTheory.LIST_REL_EL_EQN]) >>
  Cases_on `i < LENGTH args`
  >- (
    (* i < LENGTH args: use first LIST_REL *)
    simp[rich_listTheory.EL_APPEND1] >>
    qpat_x_assum `LIST_REL _ vs args` mp_tac >>
    simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
    first_x_assum drule >> strip_tac >>
    `expr_type (EL i args) = SND (EL i params)` by (
      `EL i (MAP expr_type args) = EL i (TAKE (LENGTH args) (MAP SND params))` by
        metis_tac[] >>
      gvs[listTheory.EL_MAP, rich_listTheory.EL_TAKE]) >>
    gvs[])
  >- (
    (* i >= LENGTH args: use second LIST_REL *)
    `i >= LENGTH vs` by simp[] >>
    `i - LENGTH vs < LENGTH dflt_vs` by DECIDE_TAC >>
    simp[rich_listTheory.EL_APPEND2] >>
    qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
    simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >> gvs[] >>
    `expr_type (EL (i - LENGTH vs) needed_dflts) = SND (EL i params)` by (
      `EL (i - LENGTH args) (MAP expr_type needed_dflts) =
       EL (i - LENGTH args) (MAP SND (DROP (LENGTH args) params))` by
        metis_tac[] >>
      gvs[listTheory.EL_MAP, listTheory.EL_DROP]) >>
    first_x_assum (qspec_then `i - LENGTH args` mp_tac) >>
    impl_tac >- simp[] >>
    strip_tac >> gvs[])
QED



(* bind_arguments succeeds when args are well-typed w.r.t. params *)
Theorem bind_arguments_succeeds:
  !tenv params vs.
    LENGTH params = LENGTH vs /\
    (!i. i < LENGTH params ==>
      ?tv. evaluate_type tenv (SND (EL i params)) = SOME tv /\
           value_has_type tv (EL i vs)) ==>
    ?sc. bind_arguments tenv params vs = SOME sc
Proof
  Induct_on `params`
  >- (rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def])
  >> simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  strip_tac >>
  (* Head typing from i=0 *)
  `?tv. evaluate_type tenv p_2 = SOME tv /\ value_has_type tv h` by (
    first_x_assum (qspecl_then [`0`] mp_tac) >> simp[]) >>
  imp_res_tac safe_cast_well_typed >> simp[] >>
  (* Apply IH — uses first_assum to preserve ∀i *)
  first_assum irule >> simp[] >>
  rpt strip_tac >>
  (* Shift index for tail *)
  first_x_assum (qspecl_then [`SUC i`] mp_tac) >> simp[]
QED

(* Combined: LIST_REL typing for args + defaults => bind_arguments succeeds *)
Theorem args_dflts_bind_arguments:
  !tenv (params: (string # type) list) args vs dflt_vs needed_dflts.
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) vs args /\
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) dflt_vs needed_dflts /\
    MAP expr_type args = TAKE (LENGTH args) (MAP SND params) /\
    MAP expr_type needed_dflts =
      MAP SND (DROP (LENGTH args) params) /\
    LENGTH args + LENGTH needed_dflts = LENGTH params ==>
    ?sc. bind_arguments tenv params (vs ++ dflt_vs) = SOME sc
Proof
  rpt strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  irule bind_arguments_succeeds >>
  REVERSE conj_tac >- simp[LENGTH_APPEND] >>
  gen_tac >> strip_tac >>
  Cases_on `i < LENGTH args`
  >- ( (* i < LENGTH args: get tv from LIST_REL for args *)
    qpat_x_assum `LIST_REL _ vs args` mp_tac >>
    simp[listTheory.LIST_REL_EL_EQN] >> disch_then drule >> strip_tac >>
    `EL i (MAP expr_type args) = EL i (MAP SND params)` by
      simp[rich_listTheory.EL_TAKE] >>
    qexists_tac `tv` >>
    gvs[listTheory.EL_MAP, rich_listTheory.EL_APPEND1])
  >> ( (* i >= LENGTH args: get tv from LIST_REL for defaults *)
    `i - LENGTH args < LENGTH needed_dflts` by DECIDE_TAC >>
    qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
    simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
    first_x_assum drule >> strip_tac >>
    `EL (i - LENGTH args) (MAP expr_type needed_dflts) =
     EL (i - LENGTH args) (MAP SND (DROP (LENGTH args) params))` by
      simp[] >>
    qexists_tac `tv` >>
    gvs[listTheory.EL_MAP, listTheory.EL_DROP, rich_listTheory.EL_APPEND2])
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
  `well_formed_type_value tv0` by
    metis_tac[evaluate_type_well_formed] >>
  rename1 `bind_arguments tenv params tl = SOME sc0` >>
  `scope_well_typed sc0` by (
    qpat_x_assum `!tenv vs sc. _`
      (qspecl_then [`tenv`, `tl`, `sc0`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC i`, `tv`] mp_tac) >> simp[]) >>
  gvs[scope_well_typed_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> res_tac
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


Theorem env_consistent_type_defs:
  env_consistent env cx st ==> env.type_defs = get_tenv cx
Proof
  simp[env_consistent_def]
QED

Theorem env_consistent_empty:
  !cx st.
    env_consistent
      <| var_types := FEMPTY;
         global_types := FEMPTY;
         toplevel_types := FEMPTY;
         type_defs := get_tenv cx;
         fn_sigs := FEMPTY;
         flag_members := FEMPTY |> cx st
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

Theorem well_typed_named_exprs_MAP_SND:
  !env kes. well_typed_named_exprs env kes ==>
            well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Theorem LIST_REL_EVERY_EXISTS:
  !R xs ys. LIST_REL R xs ys ==> EVERY (\x. ?y. R x y) xs
Proof
  Induct_on `xs` >> simp[LIST_REL_CONS1] >> metis_tac[]
QED

(* get_tenv is independent of cx.stk *)
Theorem get_tenv_stk_irrelevant:
  !cx f. get_tenv (cx with stk updated_by f) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem get_module_code_stk_irrelevant:
  !cx f src. get_module_code (cx with stk updated_by f) src =
             get_module_code cx src
Proof
  simp[get_module_code_def]
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
       get_tenv_stk_irrelevant, fn_sigs_consistent_stk_irrelevant,
       well_formed_type_def]
QED

Theorem context_well_typed_stk_irrelevant:
  !cx f. context_well_typed (cx with stk updated_by f) <=>
         context_well_typed cx
Proof
  simp[context_well_typed_def]
QED

Theorem lift_option_type_SOME:
  !x s st v. lift_option_type x s st = (INL v, st) ==> x = SOME v
Proof
  Cases_on `x` >> simp[lift_option_type_def, return_def, raise_def]
QED

Theorem lift_option_SOME:
  !x s st v st'. lift_option x s st = (INL v, st') ==> x = SOME v /\ st' = st
Proof
  rw[lift_option_def] >> Cases_on `x` >> gvs[return_def, raise_def]
QED

Theorem get_immutables_SOME:
  !cx src st r st'.
    get_immutables cx src st = (INL r, st') ==>
    st' = st /\ ?mods. ALOOKUP st.immutables cx.txn.target = SOME mods /\
    r = get_source_immutables src mods
Proof
  rw[get_immutables_def, get_address_immutables_def, bind_def,
     lift_option_def, return_def, raise_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
QED

Theorem get_immutables_well_typed:
  !cx src st r st'.
    get_immutables cx src st = (INL r, st') /\
    state_well_typed st ==>
    st' = st /\
    !id tv v. FLOOKUP r id = SOME (tv, v) ==>
      value_has_type tv v /\ well_formed_type_value tv
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac get_immutables_SOME >> gvs[] >>
  rpt strip_tac >>
  Cases_on `ALOOKUP mods src` >>
  gvs[get_source_immutables_def, state_well_typed_def] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  `imms_well_typed mods` by (fs[EVERY_MEM, FORALL_PROD] >> res_tac) >>
  fs[imms_well_typed_def] >> res_tac
QED

(* Extract well_typed_stmts for function body from functions_well_typed.
 * Simple version: uses FEMPTY fn_sigs (no function signatures needed). *)
Theorem functions_well_typed_body:
  !cx src_id_opt fn ts fm nr args dflts ret body.
    functions_well_typed cx /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (fm, nr, args, dflts, ret, body) ==>
    ?env_body.
      env_body.type_defs = get_tenv cx /\
      env_body.global_types = FEMPTY /\
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
Proof
  rw[functions_well_typed_def] >>
  first_x_assum (qspecl_then [`src_id_opt`, `fn`, `ts`, `fm`, `nr`, `args`,
    `dflts`, `ret`, `body`, `FEMPTY`] mp_tac) >>
  simp[fn_sigs_consistent_def, FLOOKUP_EMPTY] >>
  strip_tac >> qexists_tac `env_body` >> simp[]
QED

(* Full version: takes fn_sigs parameter (needed for IntCall where body can
 * call other functions). Exports all env_body properties including
 * toplevel_types and flag_members consistency.
 * The toplevel_types immutables condition is universally quantified over imms,
 * so it can be specialized to any specific state. *)
Theorem functions_well_typed_body_full:
  !cx src_id_opt fn ts fm nr args dflts ret body fn_sigs.
    functions_well_typed cx /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (fm, nr, args, dflts, ret, body) /\
    fn_sigs_consistent fn_sigs cx ==>
    (nr ==> cx.nonreentrant_slot <> NONE) /\
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
           fn_sigs := FEMPTY;
           flag_members := FEMPTY |> dflts /\
      (!id typ. MEM (id, typ) args ==>
         FLOOKUP env_body.var_types (string_to_num id) = SOME typ) /\
      MAP expr_type dflts =
        MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
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
      (!src fid ls.
         FLOOKUP env_body.flag_members (src, fid) = SOME ls ==>
         ?ts'. get_module_code cx src = SOME ts' /\
               lookup_flag fid ts' = SOME ls /\
               FLOOKUP (get_tenv cx) (string_to_num fid) =
                 SOME (FlagArgs (LENGTH ls)))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `functions_well_typed _`
    (strip_assume_tac o REWRITE_RULE [functions_well_typed_def]) >>
  first_x_assum (qspecl_then [`src_id_opt`, `fn`, `ts`, `fm`, `nr`, `args`,
    `dflts`, `ret`, `body`, `fn_sigs`] mp_tac) >>
  simp[] >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`env_body`, `ret_tv`] >>
  simp[] >> first_assum ACCEPT_TAC
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

(* KEY: if scopes and immutables are unchanged, state_well_typed is preserved *)
Theorem state_well_typed_scopes_immutables:
  !st st'.
    st'.scopes = st.scopes /\ st'.immutables = st.immutables /\
    state_well_typed st ==>
    state_well_typed st'
Proof
  simp[state_well_typed_def]
QED

(* KEY: if scopes and immutables are unchanged, env_consistent is preserved *)
Theorem env_consistent_scopes_immutables:
  !env cx st st'.
    st'.scopes = st.scopes /\ st'.immutables = st.immutables /\
    env_consistent env cx st ==>
    env_consistent env cx st'
Proof
  rw[env_consistent_def] >> metis_tac[]
QED

(* Combined: both preserved when scopes and immutables unchanged *)
Theorem tp_preserved_scopes_immutables:
  !env cx st st'.
    st'.scopes = st.scopes /\ st'.immutables = st.immutables /\
    state_well_typed st /\ env_consistent env cx st ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  metis_tac[state_well_typed_scopes_immutables, env_consistent_scopes_immutables]
QED

(* Tactic: prove state_well_typed/env_consistent preserved by an operation
   that only changes logs/accounts/transient (not scopes or immutables).
   defs: definitions to unfold to show scopes/immutables unchanged.
   Handles both state_well_typed and env_consistent subgoals. *)
val push_log_defs = [push_log_def, return_def];
val update_accounts_defs = [update_accounts_def, get_accounts_def,
                            return_def, bind_def];
val update_transient_defs = [update_transient_def, get_transient_storage_def,
                             return_def, bind_def];
val transfer_value_defs = [transfer_value_def, bind_def, AllCaseEqs(),
                           return_def, raise_def, update_accounts_def,
                           get_accounts_def];

(* Tactic: after IH gives state_well_typed/env_consistent for intermediate state,
   prove they hold for the final state after an op that preserves scopes+immutables.
   Usage: ... >> first_x_assum $ drule_all >> strip_tac >> tp_op_tac [op_def, ...] *)
fun tp_op_tac defs =
  gvs defs >>
  TRY (conj_tac >- (irule state_well_typed_scopes_immutables >>
                     HINT_EXISTS_TAC >> simp[])) >>
  TRY (irule env_consistent_scopes_immutables >> HINT_EXISTS_TAC >> simp[]);

(* Tactic for P7 chain builtins (RawCallTarget, RawLog, RawRevert,
   SelfDestructTarget, CreateTarget):
   eval_exprs (P8 IH) → state-preserving ops → return Value v.

   tp_chain_prefix_tac ev_thm wte_thm:
     Handles shared prefix: strip, unfold wte/ev, peel eval_exprs, apply P8 IH.
     After this, swt st1 + ec env cx st1 are in assumptions.
     Remaining goal: monadic_tail st1 = (res,st') ⇒ conclusion.

   tp_chain_tail_tac state_thms:
     After prefix, strips the tail assumption, uses imp_res_tac on
     state preservation theorems, then closes with tp_preserved_scopes_immutables.
     state_thms: list of theorems for operations in the tail (e.g.,
       [push_log_scopes, push_log_immutables]) *)
fun tp_chain_prefix_tac ev_thm wte_thm =
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[wte_thm] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_thm] >>
  simp_tac std_ss [bind_apply] >>
  Cases_on `eval_exprs cx es st` >> rename1 `(res_es, st1)` >>
  reverse (Cases_on `res_es`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rw[] >> first_x_assum drule_all >> simp[] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac;

val chain_state_thms =
  [check_state, lift_option_type_state, lift_option_state,
   get_accounts_state, get_transient_storage_state];
val chain_scopes_thms =
  [push_log_scopes, update_accounts_scopes,
   update_transient_scopes, transfer_value_scopes];
val chain_immutables_thms =
  [push_log_immutables, update_accounts_immutables,
   update_transient_immutables, transfer_value_immutables];

(* Prove scopes/immutables preservation for a monadic tail in assumptions.
   Works by unfolding bind/ignore_bind/AllCaseEqs and imp_res_tac on
   individual operation preservation theorems.
   The sub-goal is just equalities, so AllCaseEqs explosion is harmless. *)
val chain_preservation_thms =
  chain_state_thms @ chain_scopes_thms @ chain_immutables_thms;

(* For the scopes/imm subgoal, we case-split on intermediate monadic results.
   The key: use bind_apply/ignore_bind_apply to unfold one level of bind,
   then AllCaseEqs to split on INL/INR. For compound operations like
   transfer_value, we DON'T unfold -- we use imp_res_tac on their
   preservation theorems directly.

   Strategy: repeatedly rewrite top-level bind, case-split, apply imp_res_tac.
   The goal is simple (st'.scopes = st1.scopes /\ ...) so case explosion
   is bounded -- each branch is closed quickly. *)
(* Peel binds in assumptions one at a time via full_simp_tac.
   CHANGED_TAC ensures termination. After each peel, case-split with
   AllCaseEqs and apply imp_res_tac for state preservation. *)
fun chain_scopes_imm_tac () = let
  val imp_chain = MAP_EVERY (TRY o imp_res_tac) chain_preservation_thms
  val peel_step =
    CHANGED_TAC (
      full_simp_tac std_ss [Once bind_apply, Once ignore_bind_apply,
                            COND_RATOR, LET_THM, UNCURRY]) >>
    imp_chain >> gvs[AllCaseEqs(), return_def, raise_def]
in
  rpt peel_step >> imp_chain >> gvs[return_def, raise_def]
end;

(* Full tail tactic: strips tail, proves scopes/imm preserved as subgoal,
   then closes swt+ec with tp_preserved_scopes_immutables.
   value_has_type_tac: optional tactic for proving value_has_type after
   materialise. Default handles NoneV, BoolV, AddressV, BytesV. *)
fun tp_chain_tail_tac value_tac =
  strip_tac >>
  (* Step 1: Prove scopes+immutables preservation as subgoal *)
  `st'.scopes = st1.scopes /\ st'.immutables = st1.immutables` by
    chain_scopes_imm_tac () >>
  (* Step 2: swt + ec from tp_preserved_scopes_immutables *)
  `state_well_typed st' /\ env_consistent env cx st'` by (
    irule tp_preserved_scopes_immutables >>
    qexists_tac `st1` >> gvs[]) >>
  simp[] >>
  (* Step 3: value_has_type — unfold monadic tail for return value *)
  rpt strip_tac >>
  gvs[bind_apply, ignore_bind_apply, AllCaseEqs(),
      return_def, raise_def, COND_RATOR, LET_THM, UNCURRY,
      materialise_def, expr_type_def, evaluate_type_def,
      value_has_type_def, raw_call_return_type_def] >>
  value_tac;

(* Helper: type_slot_size for BytesT (Dynamic n) bounded when n < dimword(:256).
   Used to discharge evaluate_type preconditions in RawCallTarget proof. *)
Theorem bytes_slot_size_bound:
  n < dimword(:256) ==>
   type_slot_size (BaseTV (BytesT (Dynamic n))) <= dimword(:256) /\
   type_slot_size_list [BaseTV BoolT; BaseTV (BytesT (Dynamic n))] <=
     dimword(:256) /\
   type_slot_size (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))]) <=
     dimword(:256)
Proof
  strip_tac >>
  `type_slot_size (BaseTV (BytesT (Dynamic n))) + 2 <= dimword(:256)` by (
    `type_slot_size (BaseTV (BytesT (Dynamic n))) = 1 + (n + 31) DIV 32`
      by EVAL_TAC >>
    `(n + 31) DIV 32 <= (dimword(:256) - 1 + 31) DIV 32` by
      (irule DIV_LE_MONOTONE >> DECIDE_TAC) >>
    `(dimword(:256) - 1 + 31) DIV 32 + 3 <= dimword(:256)` by EVAL_TAC >>
    DECIDE_TAC) >>
  `type_slot_size_list [BaseTV BoolT; BaseTV (BytesT (Dynamic n))] =
   1 + type_slot_size (BaseTV (BytesT (Dynamic n)))` by EVAL_TAC >>
  `type_slot_size (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))]) =
   1 + type_slot_size (BaseTV (BytesT (Dynamic n)))` by
     simp[type_slot_size_def] >>
  DECIDE_TAC
QED

val default_chain_value_tac =
  gvs[listTheory.LENGTH_TAKE_EQ] >>
  TRY (imp_res_tac (REWRITE_RULE [wordsTheory.dimword_def,
         EVAL ``2 ** dimindex(:256)``] bytes_slot_size_bound) >>
       gvs[] >> NO_TAC) >>
  TRY DECIDE_TAC;

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
    (!id ty entry.
       FLOOKUP env.var_types id = SOME ty /\
       lookup_scopes id scopes = SOME entry ==>
       evaluate_type (get_tenv cx) ty = SOME entry.type) /\
    (!id ty tv v.
       FLOOKUP env.global_types id = SOME ty /\
       FLOOKUP (get_source_immutables (current_module cx)
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!src_id_opt id ty ts.
       FLOOKUP env.toplevel_types (src_id_opt, id) = SOME ty /\
       get_module_code cx src_id_opt = SOME ts ==>
       (!is_transient typ id_str.
          find_var_decl_by_num id ts =
            SOME (StorageVarDecl is_transient typ, id_str) ==>
          typ = ty) /\
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts =
            SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
          ty = NoneT) /\
       (find_var_decl_by_num id ts = NONE ==>
         !tv v. FLOOKUP (get_source_immutables src_id_opt
           (case ALOOKUP st.immutables cx.txn.target of
              SOME m => m | NONE => [])) id = SOME (tv, v) ==>
         evaluate_type (get_tenv cx) ty = SOME tv)) /\
    (!src_id_opt fid ls.
       FLOOKUP env.flag_members (src_id_opt, fid) = SOME ls ==>
       ?ts. get_module_code cx src_id_opt = SOME ts /\
            lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) =
              SOME (FlagArgs (LENGTH ls)))
Proof
  simp[env_consistent_def]
QED

(* After pop_function prev restores caller scopes, env_consistent is restored
   (assuming immutables unchanged and caller env was consistent with prev) *)
Theorem env_consistent_pop_function:
  !env cx st prev res st'.
    pop_function prev st = (res, st') /\
    env_consistent env cx (st with scopes := prev) ==>
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

(* env_consistent is preserved by evaluation steps that preserve tv and
   scope domains. Uses preserves_tv (per-scope FLOOKUP preservation) and
   MAP FDOM equality to show lookup_scopes finds the same position with
   the same tv after evaluation. *)
Theorem lookup_scopes_EL:
  !scopes id entry.
    lookup_scopes id scopes = SOME entry ==>
    ?i. i < LENGTH scopes /\
        FLOOKUP (EL i scopes) id = SOME entry /\
        !j. j < i ==> FLOOKUP (EL j scopes) id = NONE
Proof
  Induct >> simp[lookup_scopes_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> simp[]
  >- (strip_tac >> res_tac >>
      qexists_tac `SUC i` >> simp[] >>
      Cases >> simp[])
  >> strip_tac >> qexists_tac `0` >> simp[]
QED

Theorem lookup_scopes_from_EL:
  !scopes id tvv i.
    i < LENGTH scopes /\
    FLOOKUP (EL i scopes) id = SOME tvv /\
    (!j. j < i ==> FLOOKUP (EL j scopes) id = NONE) ==>
    lookup_scopes id scopes = SOME tvv
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[lookup_scopes_def, AllCaseEqs()] >>
  first_assum(qspec_then`0`mp_tac) >> simp_tac (srw_ss())[] >>
  strip_tac >> first_x_assum irule >>
  goal_assum $ drule_at Any >> rw[] >>
  first_x_assum(qspec_then`SUC j`mp_tac) >> rw[]
QED

Theorem env_consistent_preserves_tv:
  !env cx st st'.
    env_consistent env cx st /\
    preserves_tv cx st st' /\
    MAP FDOM st'.scopes = MAP FDOM st.scopes /\
    (!src n. IS_SOME (FLOOKUP (get_source_immutables src
        (case ALOOKUP st'.immutables cx.txn.target of
           SOME m => m | NONE => [])) n) ==>
             IS_SOME (FLOOKUP (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of
           SOME m => m | NONE => [])) n)) ==>
    env_consistent env cx st'
Proof
  rw[env_consistent_def] >- (
    (* var_types clause *)
    drule_at Any lookup_scopes_EL >> strip_tac >>
    rename1 `FLOOKUP (EL i st'.scopes) id = SOME entry'` >>
    `i < LENGTH st.scopes` by gvs[preserves_tv_def] >>
    `FDOM (EL i st'.scopes) = FDOM (EL i st.scopes)` by (
      imp_res_tac listTheory.MAP_EQ_EVERY2 >>
      gvs[listTheory.LIST_REL_EL_EQN, preserves_tv_def]) >>
    `?entry0. FLOOKUP (EL i st.scopes) id = SOME entry0` by
      gvs[finite_mapTheory.FLOOKUP_DEF, PULL_EXISTS] >>
    `!j. j < i ==> FLOOKUP (EL j st.scopes) id = NONE` by (
      rpt strip_tac >>
      `FDOM (EL j st'.scopes) = FDOM (EL j st.scopes)` by (
        imp_res_tac listTheory.MAP_EQ_EVERY2 >>
        gvs[listTheory.LIST_REL_EL_EQN, preserves_tv_def]) >>
      `FLOOKUP (EL j st'.scopes) id = NONE` by res_tac >>
      gvs[finite_mapTheory.FLOOKUP_DEF] >>
      first_x_assum drule >> rw[]) >>
    `lookup_scopes id st.scopes = SOME entry0` by (
      irule lookup_scopes_from_EL >>
      goal_assum drule >> simp[]) >>
    `evaluate_type (get_tenv cx) ty = SOME entry0.type` by res_tac >>
    `?entry1. FLOOKUP (EL i st'.scopes) id = SOME entry1 /\ entry1.type = entry0.type` by
      gvs[preserves_tv_def] >>
    gvs[])
  (* global_types clause *)
  >- (gvs[IS_SOME_EXISTS, PULL_EXISTS]
      >> first_x_assum drule >> strip_tac
      >> rename1 `FLOOKUP _ id = SOME old_entry`
      >> Cases_on `old_entry`
      >> rename1 `FLOOKUP _ id = SOME (tv0, v0)`
      >> `evaluate_type (get_tenv cx) ty = SOME tv0` by res_tac
      >> `∃v'. FLOOKUP (get_source_immutables (current_module cx)
           (case ALOOKUP st'.immutables cx.txn.target of
              SOME m => m | NONE => [])) id = SOME (tv0, v')` by
         gvs[preserves_tv_def]
      >> gvs[])
  (* toplevel_types clause *)
  >> rpt strip_tac
  (* StorageVarDecl sub-case: depends only on cx, trivially preserved *)
  >- res_tac
  (* HashMapVarDecl sub-case: depends only on cx, trivially preserved *)
  >- res_tac
  (* Immutable sub-case: same pattern as global_types *)
  >> gvs[IS_SOME_EXISTS, PULL_EXISTS]
  >> first_x_assum (qspecl_then [`src_id_opt`, `id`] mp_tac)
  >> simp[] >> strip_tac
  >> rename1 `FLOOKUP _ id = SOME old_entry`
  >> Cases_on `old_entry`
  >> rename1 `FLOOKUP _ id = SOME (tv0, v0)`
  >> `evaluate_type (get_tenv cx) ty = SOME tv0` by res_tac
  >> `∃v'. FLOOKUP (get_source_immutables src_id_opt
       (case ALOOKUP st'.immutables cx.txn.target of
          SOME m => m | NONE => [])) id = SOME (tv0, v')` by
     gvs[preserves_tv_def]
  >> gvs[]
QED

(* bind_arguments stores evaluate_type results *)
Theorem bind_arguments_evaluate_type:
  !tenv params vs sc n entry.
    bind_arguments tenv params vs = SOME sc /\
    FLOOKUP sc n = SOME entry ==>
    ?id typ. n = string_to_num id /\
             MEM (id, typ) params /\
             evaluate_type tenv typ = SOME entry.type
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
    env_body.global_types = FEMPTY /\
    (!src_id_opt id ty ts.
       FLOOKUP env_body.toplevel_types (src_id_opt, id) = SOME ty /\
       get_module_code cx' src_id_opt = SOME ts ==>
       (!is_transient typ id_str.
          find_var_decl_by_num id ts =
            SOME (StorageVarDecl is_transient typ, id_str) ==>
          typ = ty) /\
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts =
            SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
          ty = NoneT) /\
       (find_var_decl_by_num id ts = NONE ==>
         !tv v imms. FLOOKUP (get_source_immutables src_id_opt
           (case ALOOKUP imms cx'.txn.target of
              SOME m => m | NONE => [])) id = SOME (tv, v) ==>
         evaluate_type (get_tenv cx') ty = SOME tv)) /\
    (!src_id_opt fid ls.
       FLOOKUP env_body.flag_members (src_id_opt, fid) = SOME ls ==>
       ?ts. get_module_code cx' src_id_opt = SOME ts /\
            lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx') (string_to_num fid) =
              SOME (FlagArgs (LENGTH ls))) ==>
    env_consistent env_body cx' (st with scopes := [sc])
Proof
  rpt strip_tac >>
  simp[env_consistent_def, lookup_scopes_def, AllCaseEqs()] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      drule bind_arguments_evaluate_type >>
      disch_then drule >> strip_tac >> gvs[] >>
      res_tac >> gvs[])
  >> rpt strip_tac >> res_tac
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
    \\ gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
           sum_CASE_rator, CaseEq"prod", CaseEq"sum"]
    \\ TRY (drule lift_option_error \\ rw[])
    \\ pairarg_tac \\ gvs[bind_apply, type_check_def, assert_def,
           sum_CASE_rator, CaseEq"prod", CaseEq"sum"]
    \\ gvs[set_scopes_def, get_scopes_def, return_def, raise_def, AllCaseEqs()]
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
  (* Simplify get_address_immutables to expose ALOOKUP *)
  \\ gvs[get_address_immutables_def, lift_option_def,
         AllCaseEqs(), option_CASE_rator, raise_def, return_def]
  (* Now: ALOOKUP st.immutables cx.txn.target = SOME imms is a hyp,
     and the FLOOKUP hyp simplified to get_source_immutables src imms *)
  \\ gvs[set_address_immutables_def, return_def]
  (* Extract well_formed_type_value from the old immutables entry *)
  \\ `imms_well_typed imms` by metis_tac[state_well_typed_imms_lookup]
  \\ `well_formed_type_value tv` by metis_tac[imms_well_typed_src_lookup]
  \\ gvs[state_well_typed_def, env_consistent_def]
  \\ gvs[EVERY_MEM, alistTheory.MEM_ADELKEY, pairTheory.FORALL_PROD]
  \\ gvs[get_source_immutables_def, set_source_immutables_def]
  \\ gvs[alistTheory.ALOOKUP_ADELKEY]
  \\ gvs[imms_well_typed_def]
  \\ rw[]
  \\ gvs[finite_mapTheory.FLOOKUP_UPDATE, CaseEq"bool"]
  \\ gvs[alistTheory.ALOOKUP_ADELKEY]
  \\ TRY (res_tac >> NO_TAC)
  (* Remaining goals: need well_formed/value_has_type for a different id in same src *)
  \\ Cases_on `ALOOKUP imms src` >> gvs[]
  \\ first_x_assum (drule_all_then strip_assume_tac)
QED

(* loc_type: the runtime type stored at a target location *)

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

(* When eval_base_target returns TopLevelVar, extract the base FLOOKUP *)
Theorem eval_base_target_toplevel_flookup[local]:
  !bt cx st0 src id sbs st1 env ty.
    eval_base_target cx bt st0 = (INL (TopLevelVar src id, sbs), st1) /\
    well_typed_target env bt ty ==>
    ?base_ty. FLOOKUP env.toplevel_types (src, string_to_num id) = SOME base_ty
Proof
  Induct >> (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(), well_typed_expr_def,
        return_def, ignore_bind_apply, get_scopes_def, type_check_def, assert_def,
        option_CASE_rator, get_immutables_def, get_address_immutables_def,
        lift_option_def, optionTheory.IS_SOME_EXISTS, pairTheory.EXISTS_PROD,
        raise_def, bind_def, lift_option_type_def] >>
    TRY (pairarg_tac >> gvs[return_def] >>
         gvs[lift_option_type_def, option_CASE_rator, AllCaseEqs(), raise_def, return_def]) >>
    TRY (Cases_on `p` >> gvs[Once evaluate_def, return_def, well_typed_expr_def] >> NO_TAC) >>
    first_x_assum drule >> disch_then drule >> simp[])
QED

(* Like eval_base_target_type_connection but for TopLevelVar,
   where loc_type is F. Uses toplevel_types + evaluate_type instead. *)
Theorem eval_base_target_type_connection_toplevel[local]:
  !bt cx st0 src id sbs st1 env ty base_ty base_tv.
    eval_base_target cx bt st0 = (INL (TopLevelVar src id, sbs), st1) /\
    well_typed_target env bt ty /\
    env_consistent env cx (st:evaluation_state) /\
    FLOOKUP env.toplevel_types (src, string_to_num id) = SOME base_ty /\
    evaluate_type (get_tenv cx) base_ty = SOME base_tv ==>
    evaluate_type (get_tenv cx) ty = SOME (leaf_type base_tv (REVERSE sbs)) /\
    well_formed_type_value base_tv
Proof
  Induct
  (* NameTarget — returns ScopedVar, contradiction *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_apply, AllCaseEqs(), ignore_bind_apply,
          get_scopes_def, return_def, type_check_def, assert_def])
  (* BareGlobalNameTarget — returns ImmutableVar, contradiction *)
  >- (simp[Once evaluate_def, bind_apply, AllCaseEqs(), ignore_bind_apply,
           return_def, type_check_def, assert_def, option_CASE_rator,
           get_immutables_def, get_address_immutables_def, lift_option_def,
           optionTheory.IS_SOME_EXISTS, pairTheory.EXISTS_PROD] >>
      rpt gen_tac >> strip_tac >> gvs[raise_def, return_def])
  (* TopLevelNameTarget — base case *)
  >- (simp[pairTheory.FORALL_PROD] >>
      rw[Once evaluate_def, return_def, well_typed_expr_def] >>
      gvs[leaf_type_def] >>
      irule (cj 1 evaluate_type_well_formed) >> metis_tac[])
  (* SubscriptTarget *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
          well_typed_expr_def, bind_def, option_CASE_rator] >>
      pairarg_tac \\ gvs[bind_apply, AllCaseEqs(), return_def,
                          leaf_type_append] >>
      first_x_assum drule_all >> strip_tac >>
      gvs[lift_option_type_def, option_CASE_rator, AllCaseEqs(), raise_def] >>
      gvs[return_def] >>
      Cases_on `tgt_ty` >> gvs[subscript_type_ok_def] >>
      gvs[Once evaluate_type_def] >>
      gvs[CaseEq"option"] >>
      qpat_x_assum `_ = leaf_type _ _` (SUBST_ALL_TAC o SYM) >>
      simp[leaf_type_def])
  (* AttributeTarget *)
  >> (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
          well_typed_expr_def] >>
      gvs[bind_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def] >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `tgt_ty` >>
      gvs[attribute_type_ok_def, leaf_type_def] >>
      gvs[leaf_type_append, leaf_type_def] >>
      BasicProvers.EVERY_CASE_TAC >> gvs[evaluate_type_def] >>
      gvs[AllCaseEqs()] >>
      qpat_x_assum `StructTV _ = leaf_type _ _` (assume_tac o SYM) >>
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
      \\ pairarg_tac \\ gvs[bind_apply,CaseEq"prod",CaseEq"sum",ignore_bind_apply,
                            type_check_def, assert_def, sum_CASE_rator, AllCaseEqs()]
      \\ gvs[set_scopes_def, return_def, raise_def]
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
  \\ `?sc_entry. lookup_scopes (string_to_num s) st.scopes = SOME sc_entry`
  by (
    gvs[get_scopes_def, return_def, lift_option_def, option_CASE_rator]
    >> gvs[AllCaseEqs(), return_def, raise_def]
    >> irule_at Any find_containing_scope_lookup
    >> goal_assum drule )
  \\ pop_assum strip_assume_tac
  \\ `loc_type cx st (ScopedVar s) sc_entry.type` by (rw[loc_type_def] >> qexists_tac `sc_entry` >> simp[])
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
    \\ gvs[scope_well_typed_def, FLOOKUP_UPDATE, CaseEq"bool"]
    \\ rw[] \\ gvs[]
    \\ res_tac >> gvs[]  >>
    first_x_assum irule >>
    drule find_containing_scope_lookup >> rw[]
    >> gvs[])
  \\ irule (iffRL $ cj 1 env_consistent_scopes_only)
  \\ gvs[env_consistent_def]
  \\ rw[]
  \\ TRY (
       first_x_assum irule
       \\ goal_assum drule \\ rw[])
  \\ TRY (res_tac \\ NO_TAC)
  \\ drule find_containing_scope_structure
  \\ strip_tac \\ gvs[]
  \\ drule find_containing_scope_lookup >> rw[]
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
  (* Get value_has_type + well_formed from imms_well_typed via helpers *)
  (* Get value_has_type from imms via helpers *)
  \\ drule_all state_well_typed_imms_lookup
  \\ disch_tac
  \\ `value_has_type (FST tva) (SND tva)` by (
    Cases_on`tva` >> gvs[] >>
    drule_all imms_well_typed_src_lookup >> simp[])
  \\ drule assign_subscripts_preserves_type
  \\ simp[]
QED

Finalise assign_target_well_typed

(* Generalized assign_target_well_typed for ANY assign operation.
   The caller supplies the condition that assign_subscripts preserves types.
   This generalizes assign_target_well_typed (which handles Replace only). *)
Theorem assign_target_well_typed_ao:
  !b cx loc sbs st0 st1 ao st res st' env ty.
    eval_base_target cx b st0 = (INL (loc, sbs), st1) /\
    well_typed_target env b ty /\
    assign_target cx (BaseTargetV loc sbs) ao st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    (* The operation preserves types at the runtime location type *)
    (!tv. loc_type cx st loc tv ==>
          !a v. value_has_type tv a /\ well_formed_type_value tv /\
                assign_subscripts tv a (REVERSE sbs) ao = INL v ==>
                value_has_type tv v) ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc` >> gvs[assign_target_def, LET_THM]
  (* ScopedVar: fully decompose monadic chain *)
  >- (
    gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
    >> TRY(imp_res_tac get_scopes_result >> gvs[])
    >> TRY(imp_res_tac lift_option_type_state >> gvs[])
    >> TRY(imp_res_tac lift_sum_state >> gvs[])
    >> TRY(imp_res_tac assign_result_state >> gvs[])
    >> gvs[bind_def, CaseEq"prod", CaseEq"sum"]
    >> TRY(imp_res_tac lift_option_state >> gvs[])
    >> pairarg_tac
    >> gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply,
           type_check_def, assert_def, sum_CASE_rator, AllCaseEqs()]
    >> gvs[set_scopes_def, return_def, raise_def]
    >> TRY(imp_res_tac lift_sum_state >> gvs[])
    >> imp_res_tac assign_result_state >> gvs[]
    >> suspend "ScopedVar")
  (* ImmutableVar: fully decompose monadic chain *)
  >- (
    gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
    >> TRY(imp_res_tac get_immutables_state >> gvs[])
    >> TRY(imp_res_tac lift_option_type_state >> gvs[])
    >> TRY(imp_res_tac lift_sum_state >> gvs[])
    >> TRY(imp_res_tac assign_result_state >> gvs[])
    >> suspend "ImmutableVar")
  (* TopLevelVar: just unfold assign_target for TopLevelVar, suspend raw *)
  >> gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
  >> TRY(imp_res_tac lookup_global_state >> gvs[])
  >> TRY(imp_res_tac lift_option_type_state >> gvs[])
  >> suspend "TopLevelVar"
QED

(* ScopedVar: now the monadic chain is fully decomposed *)
Resume assign_target_well_typed_ao[ScopedVar]:
  sg `?sc_entry. lookup_scopes (string_to_num s) s''.scopes = SOME sc_entry`
  >- (
    gvs[lift_option_def, option_CASE_rator, AllCaseEqs(), return_def, raise_def]
    >> irule_at Any find_containing_scope_lookup
    >> goal_assum drule )
  \\ pop_assum strip_assume_tac
  \\ `loc_type cx s'' (ScopedVar s) sc_entry.type` by (rw[loc_type_def] >> qexists_tac `sc_entry` >> simp[])
  \\ gvs[well_typed_atarget_def]
  \\ drule_all eval_base_target_type_connection \\ strip_tac \\ gvs[]
  \\ drule_at Any lookup_scopes_well_typed
  \\ impl_tac >- gvs[state_well_typed_def]
  \\ gvs[lift_sum_def, sum_CASE_rator, CaseEq"sum", raise_def, return_def]
  \\ strip_tac
  \\ gvs[lift_option_def,AllCaseEqs(),option_CASE_rator,raise_def,return_def]
  \\ drule find_containing_scope_lookup >> strip_tac
  \\ `value_has_type sc_entry.type a'` by (
    first_x_assum drule \\ disch_then irule \\ gvs[]
    \\ goal_assum drule \\ simp[])
  \\ conj_tac
  >- (
    irule state_well_typed_with_scopes
    \\ drule find_containing_scope_structure \\ strip_tac
    \\ gvs[state_well_typed_def, scope_well_typed_def,
           FLOOKUP_UPDATE, CaseEq"bool"]
    \\ rw[] \\ gvs[] \\ res_tac )
  \\ irule (iffRL $ cj 1 env_consistent_scopes_only)
  \\ gvs[env_consistent_def]
  \\ rw[]
  \\ TRY (first_x_assum irule \\ goal_assum drule \\ rw[])
  \\ TRY (res_tac \\ NO_TAC)
  \\ drule find_containing_scope_structure \\ strip_tac \\ gvs[]
  \\ Cases_on `string_to_num s = id`
  >- (
    drule find_containing_scope_pre_none \\ strip_tac
    \\ drule lookup_scopes_update \\ strip_tac \\ gvs[]
    \\ first_x_assum (drule_then irule) \\ goal_assum drule )
  \\ drule lookup_scopes_update_other \\ strip_tac
  \\ first_x_assum(drule_then irule) \\ gvs[]
QED

Resume assign_target_well_typed_ao[ImmutableVar]:
  markerLib.RESUME_TAC
  (* Goal 1: set_immutable error case — state unchanged *)
  >- (imp_res_tac set_immutable_error_state \\ gvs[])
  (* Goal 2: set_immutable success case *)
  \\ imp_res_tac lift_option_type_SOME
  (* Establish loc_type while get_immutables is still intact *)
  \\ `loc_type cx s'' (ImmutableVar s) (FST tva)` by (
    PURE_REWRITE_TAC[loc_type_def]
    \\ Cases_on `tva`
    \\ MAP_EVERY qexists_tac [`imms`, `r`]
    \\ ASM_REWRITE_TAC[])
  \\ imp_res_tac get_immutables_SOME \\ gvs[]
  \\ qpat_x_assum `lift_sum _ _ = _`
       (mp_tac o REWRITE_RULE[lift_sum_def])
  \\ Cases_on `assign_subscripts (FST tva) (SND tva) (REVERSE sbs) ao`
  \\ gvs[return_def, raise_def] \\ strip_tac \\ gvs[]
  \\ `value_has_type (FST tva) (SND tva) /\ well_formed_type_value (FST tva)` by (
    drule state_well_typed_imms_lookup \\ disch_then drule \\ strip_tac
    \\ Cases_on `tva` \\ gvs[]
    \\ drule_all imms_well_typed_src_lookup \\ simp[])
  \\ `value_has_type (FST tva) a'` by (
    first_x_assum drule \\ disch_then match_mp_tac
    \\ qexists_tac `SND tva` \\ simp[])
  \\ irule set_immutable_well_typed
  \\ rpt (first_x_assum (irule_at Any))
  \\ gvs[get_immutables_def, bind_apply, return_def,
         get_address_immutables_def, lift_option_def,
         CaseEq"option", option_CASE_rator]
  \\ qexists_tac `SND tva` \\ Cases_on `tva` \\ gvs[]
QED

(* Simpset for decomposing monadic chains in the CONCLUSION.
   bind_apply works for single-variable binds.
   For pair-pattern binds, use bind_decompose_full_ss instead. *)
val bind_decompose_ss =
  [bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply,
   return_def, raise_def];

(* Consolidated state-identity + terminal preservation tactic.
   Derives st' = st from state-identity operations, substitutes via gvs[],
   then applies terminal lemmas (write_storage_slot, set_global). *)
val state_identity_preserves_tac =
  rpt strip_tac
  >> TRY (imp_res_tac lift_option_type_state >> gvs[])
  >> TRY (imp_res_tac lift_sum_state >> gvs[])
  >> TRY (imp_res_tac read_storage_slot_state >> gvs[])
  >> TRY (imp_res_tac resolve_array_element_state >> gvs[])
  >> TRY (imp_res_tac assign_result_state >> gvs[])
  >> TRY (imp_res_tac check_state >> gvs[])
  >> TRY (imp_res_tac get_storage_backend_state >> gvs[])
  >> TRY (imp_res_tac lookup_global_state >> gvs[])
  >> TRY (imp_res_tac return_state >> gvs[])
  >> TRY (imp_res_tac raise_state >> gvs[])
  >> TRY (imp_res_tac write_storage_slot_well_typed >> gvs[])
  >> TRY (imp_res_tac set_global_well_typed >> gvs[])
  >> TRY (res_tac >> gvs[]);

(* Simpset for full monadic chain decomposition including pair-pattern binds.
   bind_def (not bind_apply) + UNCURRY + EXISTS_PROD handles \(a,b) <- f patterns.
   bind_apply's non-eta LHS (\v. g v) won't match UNCURRY continuations. *)
val bind_decompose_full_ss =
  [bind_def, ignore_bind_def, return_def, raise_def,
   UNCURRY, EXISTS_PROD,
   CaseEq"prod", CaseEq"sum", CaseEq"type_value",
   CaseEq"assign_operation", CaseEq"bound",
   CaseEq"option", CaseEq"bool",
   PULL_EXISTS];

Resume assign_target_well_typed_ao[TopLevelVar]:
  markerLib.RESUME_TAC
  \\ Cases_on `tv` \\ gvs[]
  (* Value + HashMapRef: single-var binds, decomposed by bind_decompose_ss *)
  \\ gvs bind_decompose_ss \\ state_identity_preserves_tac
  (* Remaining goals: HashMapRef + ArrayRef. do-block in assumptions.
     Move to conclusion and decompose. Two rounds needed:
     1st round peels outer bind, 2nd round handles inner case+bind chains.
     Key: use bind_def (not bind_apply) + UNCURRY + EXISTS_PROD
     because pair-pattern binds don't match bind_apply's non-eta LHS. *)
  \\ qpat_x_assum `_ s'' = (res, st')` mp_tac
  \\ simp bind_decompose_full_ss
  \\ rpt strip_tac \\ gvs[]
  \\ state_identity_preserves_tac
  (* ArrayRef: inner chain has (case p_1' of ...) s'' = (res, st') in asms.
     Split on p_1' and ao, decompose do-blocks, resolve state identities,
     then write_storage_slot_well_typed closes all remaining goals. *)
  \\ qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac
  \\ rpt BasicProvers.TOP_CASE_TAC
  \\ simp bind_decompose_full_ss
  \\ rpt strip_tac \\ gvs[]
  (* Collapse intermediate states, apply write_storage_slot_well_typed,
     then assign_result_state + return_state close final goals. *)
  \\ TRY (imp_res_tac read_storage_slot_state >> gvs[])
  \\ TRY (imp_res_tac lift_sum_state >> gvs[])
  \\ TRY (imp_res_tac check_state >> imp_res_tac get_storage_backend_state
          >> gvs[])
  \\ TRY (imp_res_tac write_storage_slot_well_typed >> gvs[])
  \\ imp_res_tac assign_result_state \\ gvs[]
QED

Finalise assign_target_well_typed_ao

(* assign_target preserves state_well_typed + env_consistent WITHOUT typing.
   Derives well_formed_type_value from state_well_typed directly.
   The caller provides that assign_subscripts preserves value_has_type. *)
Theorem assign_target_preserves_swt_ec:
  !cx loc sbs ao st res st' env.
    assign_target cx (BaseTargetV loc sbs) ao st = (res, st') /\
    state_well_typed st /\ env_consistent env cx st /\
    (!tv a v. value_has_type tv a /\ well_formed_type_value tv /\
              assign_subscripts tv a (REVERSE sbs) ao = INL v ==>
              value_has_type tv v) ==>
    state_well_typed st' /\ env_consistent env cx st'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc` >> gvs[assign_target_def, LET_THM]
  (* ScopedVar: decompose monadic chain, suspend for proof *)
  >- (
    gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
    >> TRY(imp_res_tac get_scopes_result >> gvs[])
    >> TRY(imp_res_tac lift_option_type_state >> gvs[])
    >> TRY(imp_res_tac lift_sum_state >> gvs[])
    >> TRY(imp_res_tac assign_result_state >> gvs[])
    >> gvs[bind_def, CaseEq"prod", CaseEq"sum"]
    >> TRY(imp_res_tac lift_option_state >> gvs[])
    >> pairarg_tac
    >> gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply,
           type_check_def, assert_def, sum_CASE_rator, AllCaseEqs()]
    >> gvs[set_scopes_def, return_def, raise_def]
    >> TRY(imp_res_tac lift_sum_state >> gvs[])
    >> imp_res_tac assign_result_state >> gvs[]
    >> suspend "ScopedVar")
  (* ImmutableVar: decompose monadic chain, suspend for proof *)
  >- (
    gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
    >> TRY(imp_res_tac get_immutables_state >> gvs[])
    >> TRY(imp_res_tac lift_option_type_state >> gvs[])
    >> TRY(imp_res_tac lift_sum_state >> gvs[])
    >> TRY(imp_res_tac assign_result_state >> gvs[])
    >> suspend "ImmutableVar")
  (* TopLevelVar: storage ops only, scopes/immutables unchanged *)
  >> gvs[bind_apply, CaseEq"prod", CaseEq"sum", ignore_bind_apply]
  >> TRY(imp_res_tac lookup_global_state >> gvs[])
  >> TRY(imp_res_tac lift_option_type_state >> gvs[])
  >> suspend "TopLevelVar"
QED

Resume assign_target_preserves_swt_ec[ScopedVar]:
  (* From find_containing_scope, establish lookup_scopes *)
  sg `?sc_entry. lookup_scopes (string_to_num s) s''.scopes = SOME sc_entry`
  >- (
    qpat_x_assum `lift_option _ _ _ = _` mp_tac
    >> gvs[lift_option_def, option_CASE_rator, AllCaseEqs(), return_def, raise_def]
    >> strip_tac
    >> irule_at Any find_containing_scope_lookup
    >> goal_assum drule )
  \\ pop_assum strip_assume_tac
  (* From state_well_typed + lookup_scopes, get value_has_type + well_formed *)
  \\ drule_at Any lookup_scopes_well_typed
  \\ impl_tac >- gvs[state_well_typed_def]
  \\ strip_tac
  (* From lift_sum, get assign_subscripts = INL a' *)
  \\ qpat_x_assum `lift_sum _ _ = _` mp_tac
  \\ gvs[lift_sum_def, sum_CASE_rator, CaseEq"sum", raise_def, return_def]
  \\ strip_tac
  (* Apply the type-preservation hypothesis *)
  \\ gvs[lift_option_def, AllCaseEqs(), option_CASE_rator, raise_def, return_def]
  \\ drule find_containing_scope_lookup >> strip_tac
  \\ `value_has_type sc_entry.type a'` by (
    first_x_assum drule \\ disch_then irule \\ gvs[]
    \\ goal_assum drule \\ simp[])
  (* Now show state_well_typed for updated scopes *)
  \\ conj_tac
  >- (
    irule state_well_typed_with_scopes
    \\ drule find_containing_scope_structure \\ strip_tac
    \\ gvs[state_well_typed_def, scope_well_typed_def,
           FLOOKUP_UPDATE, CaseEq"bool"]
    \\ rw[] \\ gvs[]
    \\ res_tac >> gvs[]
    >> first_x_assum irule
    >> drule find_containing_scope_lookup >> rw[]
    >> gvs[])
  (* Show env_consistent for updated scopes *)
  \\ irule (iffRL $ cj 1 env_consistent_scopes_only)
  \\ gvs[env_consistent_def]
  \\ rw[]
  \\ TRY (first_x_assum irule \\ goal_assum drule \\ rw[])
  \\ TRY (res_tac \\ NO_TAC)
  \\ drule find_containing_scope_structure \\ strip_tac \\ gvs[]
  \\ drule find_containing_scope_lookup >> rw[]
  \\ Cases_on `string_to_num s = id`
  >- (
    drule find_containing_scope_pre_none \\ strip_tac
    \\ drule lookup_scopes_update \\ strip_tac \\ gvs[]
    \\ first_x_assum (drule_then irule) \\ goal_assum drule )
  \\ drule lookup_scopes_update_other \\ strip_tac
  \\ first_x_assum(drule_then irule) \\ gvs[]
QED

Resume assign_target_preserves_swt_ec[ImmutableVar]:
  markerLib.RESUME_TAC
  (* Goal 1: set_immutable error case — state unchanged *)
  >- (imp_res_tac set_immutable_error_state \\ gvs[])
  (* Goal 2: set_immutable success case *)
  \\ imp_res_tac lift_option_type_SOME
  \\ imp_res_tac get_immutables_SOME \\ gvs[]
  \\ qpat_x_assum `lift_sum _ _ = _`
       (mp_tac o REWRITE_RULE[lift_sum_def])
  \\ Cases_on `assign_subscripts (FST tva) (SND tva) (REVERSE sbs) ao`
  \\ gvs[return_def, raise_def] \\ strip_tac \\ gvs[]
  \\ `value_has_type (FST tva) (SND tva) /\ well_formed_type_value (FST tva)` by (
    drule state_well_typed_imms_lookup \\ disch_then drule \\ strip_tac
    \\ Cases_on `tva` \\ gvs[]
    \\ drule_all imms_well_typed_src_lookup \\ simp[])
  \\ `value_has_type (FST tva) a'` by (
    first_x_assum match_mp_tac
    \\ qexists_tac `SND tva` \\ simp[])
  \\ irule set_immutable_well_typed
  \\ rpt (first_x_assum (irule_at Any))
  \\ gvs[get_immutables_def, bind_apply, return_def,
         get_address_immutables_def, lift_option_def,
         CaseEq"option", option_CASE_rator]
  \\ qexists_tac `SND tva` \\ Cases_on `tva` \\ gvs[]
QED

Resume assign_target_preserves_swt_ec[TopLevelVar]:
  markerLib.RESUME_TAC
  \\ Cases_on `tv` \\ gvs[]
  \\ gvs bind_decompose_ss \\ state_identity_preserves_tac
  \\ qpat_x_assum `_ s'' = (res, st')` mp_tac
  \\ simp bind_decompose_full_ss
  \\ rpt strip_tac \\ gvs[]
  \\ state_identity_preserves_tac
  \\ qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac
  \\ rpt BasicProvers.TOP_CASE_TAC
  \\ simp bind_decompose_full_ss
  \\ rpt strip_tac \\ gvs[]
  \\ TRY (imp_res_tac read_storage_slot_state >> gvs[])
  \\ TRY (imp_res_tac lift_sum_state >> gvs[])
  \\ TRY (imp_res_tac check_state >> imp_res_tac get_storage_backend_state
          >> gvs[])
  \\ TRY (imp_res_tac write_storage_slot_well_typed >> gvs[])
  \\ imp_res_tac assign_result_state \\ gvs[]
QED

Finalise assign_target_preserves_swt_ec

(* === General tactics for state_well_typed preservation ===
   Used within type_preservation Resume blocks. *)

(* For cases where eval is just return/raise (st' = st): Pass, Continue, Break,
   Return NONE, stmts[], targets[], for[], exprs[], Literal *)
val swt_trivial_tac =
  rpt gen_tac >> rpt strip_tac >>
  gvs[evaluate_def, return_def, raise_def];

(* Resolve state equalities from ALL pure monadic operations.
   Derives st' = st from matching assumptions, then substitutes. *)
val swt_resolve_state_tac =
  TRY (imp_res_tac materialise_state) >>
  TRY (imp_res_tac lift_option_type_state) >>
  TRY (imp_res_tac lift_option_state) >>
  TRY (imp_res_tac lift_sum_state) >>
  TRY (imp_res_tac check_state) >>
  TRY (imp_res_tac type_check_state) >>
  TRY (imp_res_tac get_scopes_result) >>
  TRY (imp_res_tac get_accounts_state) >>
  TRY (imp_res_tac get_transient_storage_state) >>
  TRY (imp_res_tac get_immutables_state) >>
  TRY (imp_res_tac lookup_global_state) >>
  TRY (imp_res_tac lookup_flag_mem_state) >>
  TRY (imp_res_tac switch_BoolV_state) >>
  TRY (imp_res_tac check_array_bounds_state) >>
  TRY (imp_res_tac resolve_array_element_state) >>
  TRY (imp_res_tac assign_result_state) >>
  TRY (imp_res_tac toplevel_array_length_state) >>
  TRY (imp_res_tac get_Value_state) >>
  TRY (imp_res_tac handle_loop_exception_state) >>
  gvs[];

(* General tactic: unfold evaluate_def, decompose monadic chain,
   resolve pure state equalities, apply IHs, handle state-modifying ops. *)
(* Phase 3: resolve state_well_typed for state-modifying ops.
   After IH gives state_well_typed for intermediate states, remaining
   ops (push_log, update_accounts, etc.) only change non-scopes/immutables fields.
   irule state_well_typed_scopes_immutables reduces to field equalities,
   which are resolved by unfolding the op definitions. *)
(* swt_modify_tac: resolve state_well_typed (+ env_consistent) for
   non-scope/immutable state ops (push_log, update_accounts, etc.).
   Handles both bare state_well_typed goals and conjunctions with env_consistent. *)
val swt_modify_solve =
  let val field_simp =
        gvs[push_log_def, update_accounts_def, update_transient_def,
            return_def, bind_def, ignore_bind_def, get_accounts_def,
            check_def, type_check_def, assert_def, AllCaseEqs()] >>
        TRY (imp_res_tac push_log_scopes >> gvs[]) >>
        TRY (imp_res_tac transfer_value_scopes >> gvs[]) >>
        TRY (imp_res_tac update_accounts_scopes >> gvs[]) >>
        TRY (imp_res_tac update_transient_scopes >> gvs[])
  in
    (* Try combined first (conjunction), then individual *)
    TRY (irule tp_preserved_scopes_immutables >>
         rpt (first_x_assum (irule_at Any)) >> field_simp) >>
    TRY (irule state_well_typed_scopes_immutables >>
         first_x_assum (irule_at Any) >> field_simp) >>
    TRY (irule env_consistent_scopes_immutables >>
         rpt (first_x_assum (irule_at Any)) >> field_simp)
  end;
val swt_modify_tac = swt_modify_solve;

val swt_general_tac =
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(),
      return_def, raise_def, ignore_bind_def,
      switch_BoolV_def, COND_RATOR] >>
  swt_resolve_state_tac >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* Phase 2: IH application *)
  rpt (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  swt_resolve_state_tac >>
  (* Phase 3: state-modifying ops (only if goals remain) *)
  TRY swt_modify_tac;

(* === Not-ReturnException lemmas ===
   Pure monadic ops never produce ReturnException. Used to discharge
   the "res = INR (ReturnException v) ==> ..." obligation in P0 cases. *)

Theorem pure_op_not_return:
  (!x str st e st'. lift_option_type x str st = (INR e, st') ==>
                    !v. e <> ReturnException v) /\
  (!x str st e st'. lift_option x str st = (INR e, st') ==>
                    !v. e <> ReturnException v) /\
  (!x st e st'. lift_sum x st = (INR e, st') ==>
                !v. e <> ReturnException v) /\
  (!b str st e st'. check b str st = (INR e, st') ==>
                    !v. e <> ReturnException v) /\
  (!b str st e st'. type_check b str st = (INR e, st') ==>
                    !v. e <> ReturnException v) /\
  (!tv st e st'. get_Value tv st = (INR e, st') ==>
                 !v. e <> ReturnException v)
Proof
  rpt conj_tac >> rpt gen_tac >>
  TRY (Cases_on `x`) >> TRY (Cases_on `tv`) >>
  simp[lift_option_type_def, lift_option_def, lift_sum_def,
       check_def, type_check_def, assert_def,
       get_Value_def, return_def, raise_def] >> rw[]
QED

val [lift_option_type_not_return, lift_option_not_return,
     lift_sum_not_return, check_not_return, type_check_not_return,
     get_Value_not_return] = CONJUNCTS pure_op_not_return;

(* Resolve applied case expressions in monadic goals *)
val resolve_applied_cases_tac =
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]);

Theorem eval_expr_Name_state:
  !cx t id st res st'.
    eval_expr cx (Name t id) st = (res, st') ==> st' = st
Proof
  rw[Once evaluate_def, bind_def, get_scopes_def, return_def,
     lift_option_type_def, raise_def] >>
  resolve_applied_cases_tac
QED

Theorem eval_expr_BareGlobalName_state:
  !cx t id st res st'.
    eval_expr cx (BareGlobalName t id) st = (res, st') ==> st' = st
Proof
  rw[Once evaluate_def, bind_def, return_def, lift_option_type_def, raise_def] >>
  resolve_applied_cases_tac >>
  imp_res_tac get_immutables_state
QED

Theorem eval_expr_TopLevelName_state:
  !cx t nsid st res st'.
    eval_expr cx (TopLevelName t nsid) st = (res, st') ==> st' = st
Proof
  Cases_on `nsid` >>
  rw[Once evaluate_def, bind_def, return_def] >>
  imp_res_tac lookup_global_state
QED

Theorem eval_expr_FlagMember_state:
  !cx t nsid mid st res st'.
    eval_expr cx (FlagMember t nsid mid) st = (res, st') ==> st' = st
Proof
  Cases_on `nsid` >>
  rw[Once evaluate_def, bind_def, return_def] >>
  imp_res_tac lookup_flag_mem_state
QED


(* eval_preserves_swt REMOVED: state_well_typed is proved directly
   in type_preservation's mutual induction, where the IH provides both
   state_well_typed and env_consistent for sub-evaluations. *)


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
  >> conj_tac >- simp[] (* Raise *)
  >> conj_tac >- simp[] (* Raise *)
  >> conj_tac >- simp[] (* Assert *)
  >> conj_tac >- simp[] (* Assert *)
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
  (* Chain interaction builtins *)
  >> conj_tac >- suspend "RawCallTarget_nr"
  >> conj_tac >- suspend "RawLog_nr"
  >> conj_tac >- suspend "RawRevert_nr"
  >> conj_tac >- suspend "SelfDestruct_nr"
  >> conj_tac >- suspend "CreateTarget_nr"
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

(* try f handle_function never returns ReturnException *)
Theorem try_handle_function_no_return[local]:
  !f s res s'.
    try f handle_function s = (res, s') ==>
    !v. res <> INR (ReturnException v)
Proof
  rw[try_def] >>
  Cases_on `f s` >> Cases_on `q` >> gvs[] >>
  gvs[handle_function_def, return_def, raise_def] >>
  Cases_on `y` >> gvs[handle_function_def, return_def, raise_def]
QED

(* finally preserves no-return: if neither f nor g returns ReturnException,
   then finally f g never does either *)
Theorem finally_no_return[local]:
  !f g s res s'.
    finally f g s = (res, s') /\
    (!res' s''. f s = (res', s'') ==> !v. res' <> INR (ReturnException v)) /\
    (!s0 res0 s0'. g s0 = (res0, s0') ==> !v. res0 <> INR (ReturnException v))
    ==>
    !v. res <> INR (ReturnException v)
Proof
  rw[finally_def] >>
  Cases_on `f s` >> Cases_on `q` >> gvs[] >>
  gvs[ignore_bind_def, bind_def] >>
  Cases_on `g r` >> Cases_on `q` >> gvs[return_def, raise_def] >>
  first_x_assum drule >> simp[]
QED

(* The full IntCall no-return chain *)
Theorem intcall_no_return[local]:
  !f g s res s'.
    (case finally (try f handle_function) g s of
       (INL rv, s'') =>
         (case lift_option_type (safe_cast rtv rv) msg s'' of
            (INL crv, s'') => (INL (Value crv), s'')
          | (INR e, s'') => (INR e, s''))
     | (INR e, s'') => (INR e, s'')) = (res, s') /\
    (!s0 res0 s0'. g s0 = (res0, s0') ==> !v. res0 <> INR (ReturnException v))
    ==>
    !v. res <> INR (ReturnException v)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(case _ of _ => _) = _` mp_tac >>
  simp[finally_def, try_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[ignore_bind_def, bind_def, handle_function_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* Goals 1&2: lift_option_type contradiction *)
  TRY (Cases_on `safe_cast rtv x` >>
       gvs[lift_option_type_def, return_def, raise_def] >> NO_TAC) >>
  (* Goal 3: handle_function contradiction -- case split on exception *)
  qpat_x_assum `handle_function _ _ = _` mp_tac >>
  Cases_on `y` >>
  simp[handle_function_def, return_def, raise_def]
QED

Theorem acquire_nonreentrant_lock_not_return[local]:
  !addr slot iv s res s'.
    acquire_nonreentrant_lock addr slot iv s = (res, s') ==>
    !v. res <> INR (ReturnException v)
Proof
  rw[acquire_nonreentrant_lock_def, bind_def,
     get_transient_storage_def, return_def, raise_def,
     update_transient_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem pop_function_return_not_return[local]:
  !(prev:scope list) s res s'.
    (do pop_function prev; return () od) s = (res, s') ==>
    !v. res <> INR (ReturnException v)
Proof
  rw[pop_function_def, set_scopes_def, bind_def,
     ignore_bind_def, return_def]
QED

Theorem release_nonreentrant_lock_not_return[local]:
  !addr slot s res s'.
    release_nonreentrant_lock addr slot s = (res, s') ==>
    !v. res <> INR (ReturnException v)
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def]
QED

Theorem pop_function_release_lock_not_return[local]:
  !(prev:scope list) addr slot s res s'.
    (do pop_function prev; release_nonreentrant_lock addr slot od) s = (res, s') ==>
    !v. res <> INR (ReturnException v)
Proof
  rw[pop_function_def, set_scopes_def, bind_def, ignore_bind_def,
     release_nonreentrant_lock_def, get_transient_storage_def,
     update_transient_def, return_def]
QED

Resume evaluate_no_return[IntCall_nr]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  (* Pop IHs to separate them from case analysis *)
  ntac 3 (pop_assum mp_tac) >>
  (* Rewrite eval_expr in the goal (IHs now as implications, no case exprs in assumptions) *)
  simp_tac std_ss [cj 49 evaluate_def] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, LET_THM,
      check_def, assert_def, type_check_def, get_scopes_def,
      push_function_def, return_def, raise_def,
      lift_option_type_def] >>
  (* Case-split the big nested case expression *)
  rpt (BasicProvers.PURE_CASE_TAC >> fs[raise_def, return_def]) >>
  rpt strip_tac >> gvs[] >>
  (* eval_exprs IH goals + option/if contradictions *)
  TRY (metis_tac[]) >>
  TRY (rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def, return_def]) >> NO_TAC) >>
  (* Category A: acquire_nonreentrant_lock can never produce ReturnException *)
  TRY (imp_res_tac acquire_nonreentrant_lock_not_return >> gvs[] >> NO_TAC) >>
  (* Category B: finally (try ... handle_function) cleanup = (INR (ReturnException v), ...)
     The finally assumption is present. drule finally_no_return matches it,
     leaving us to prove (1) try f handle_function and (2) cleanup g
     never produce ReturnException. *)
  first_x_assum (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] finally_no_return)) >>
  (impl_tac >- (
    rpt strip_tac >>
    imp_res_tac try_handle_function_no_return)) >>
  (impl_tac >- (
    rpt strip_tac >>
    TRY (imp_res_tac pop_function_return_not_return >> gvs[] >> NO_TAC) >>
    imp_res_tac pop_function_release_lock_not_return >> gvs[])) >>
  simp[]
QED

(* Chain-interaction builtin no-return cases: all 5 start with eval_exprs
   then do state ops that only produce Error, never ReturnException. *)
(* Tactic for chain builtin no-return cases: unfold chain ops that always
   succeed (get_accounts, get_transient, update_*, push_log, check, assert)
   or produce Error (transfer_value), never ReturnException.
   After enr_tac strips the outer eval_exprs layer, this handles the rest. *)
val chain_enr_tac =
  rpt strip_tac >>
  gvs[get_transient_storage_def, get_accounts_def, return_def, raise_def,
      push_log_def, check_def, assert_def, update_accounts_def,
      update_transient_def, ignore_bind_apply, bind_def, AllCaseEqs(),
      COND_RATOR, run_ext_call_def] >>
  TRY (drule transfer_value_error >> gvs[] >> NO_TAC) >>
  TRY (PairCases_on`result` >>
       gvs[update_accounts_def, update_transient_def, return_def, raise_def,
           ignore_bind_apply, bind_def, AllCaseEqs(), assert_def,
           push_log_def, COND_RATOR]);

Resume evaluate_no_return[RawCallTarget_nr]:
  enr_tac >> chain_enr_tac
QED
Resume evaluate_no_return[RawLog_nr]:
  enr_tac >> chain_enr_tac
QED
Resume evaluate_no_return[RawRevert_nr]:
  enr_tac
QED
Resume evaluate_no_return[SelfDestruct_nr]:
  enr_tac >> chain_enr_tac
QED
Resume evaluate_no_return[CreateTarget_nr]:
  enr_tac >> chain_enr_tac
QED

Resume evaluate_no_return[exprs_nil_nr]: enr_tac
QED

Resume evaluate_no_return[exprs_cons_nr]:
  enr_tac \\ strip_tac \\ gvs[]
  \\ first_x_assum drule_all \\ rw[]
QED

Finalise evaluate_no_return

(* ===== Relocated helpers (from within type_preservation Resume blocks) ===== *)

Theorem subscript_type_ok_evaluate:
  !ct it rt tenv atv.
    subscript_type_ok ct it rt /\
    evaluate_type tenv ct = SOME atv ==>
    ?rtv. evaluate_type tenv rt = SOME rtv
Proof
  Cases >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
  (* EVERY ($= rt) l /\ l <> [] implies MEM rt l *)
  Cases_on `l` >> gvs[] >>
  gvs[IS_SOME_EXISTS]
QED

Theorem subscript_type_ok_not_NoneTV:
  !ct it rt tenv tv.
    subscript_type_ok ct it rt /\ evaluate_type tenv ct = SOME tv ==> tv <> NoneTV
Proof
  Cases >> simp[subscript_type_ok_def, evaluate_type_def, AllCaseEqs()]
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

(* ===== Helpers for decode_value_well_typed ===== *)

(* decode_base_from_slot produces well-typed values for slot-decodable types.
   StringT, BytesT Dynamic, TupleTV, ArrayTV, StructTV are NOT slot-decodable
   (decode_base_from_slot returns NoneV for them). *)
Theorem decode_base_from_slot_well_typed[local]:
  !slot tv. well_formed_type_value tv /\
    (!n. tv <> BaseTV (StringT n)) /\
    (!n. tv <> BaseTV (BytesT (Dynamic n))) /\
    (!tvs. tv <> TupleTV tvs) /\
    (!tv0 b. tv <> ArrayTV tv0 b) /\
    (!fs. tv <> StructTV fs) ==>
    value_has_type tv (decode_base_from_slot slot tv)
Proof
  ho_match_mp_tac decode_base_from_slot_ind >>
  simp[decode_base_from_slot_def, value_has_type_inv,
       well_formed_type_value_def,
       truncate_unsigned_range,
       word_to_bytes_be_def, LENGTH_word_to_bytes,
       LENGTH_TAKE_EQ, MIN_DEF] >>
  rw[] >> TRY (irule truncate_signed_range >> simp[])
QED

(* slots_to_bytes never returns more than n bytes *)
Theorem slots_to_bytes_length[local]:
  !n slots. LENGTH (slots_to_bytes n slots) <= n
Proof
  ho_match_mp_tac slots_to_bytes_ind >>
  rw[slots_to_bytes_def, word_to_bytes_be_def, LENGTH_word_to_bytes,
     LET_THM, LENGTH_TAKE_EQ, MIN_DEF, LENGTH_APPEND]
QED

(* decode_dyn_bytes returns bytes of length ≤ max *)
Theorem decode_dyn_bytes_length[local]:
  !storage offset max bs.
    decode_dyn_bytes storage offset max = SOME bs ==> LENGTH bs <= max
Proof
  simp[decode_dyn_bytes_def, LET_THM] >> rpt strip_tac >>
  irule LESS_EQ_TRANS >> qexists_tac `w2n (lookup_storage (n2w offset) storage)` >>
  simp[slots_to_bytes_length]
QED

(* enumerate_static_array produces sorted keys *)
Theorem enumerate_static_array_sorted_aux[local]:
  !d n vs. SORTED $< (MAP FST (enumerate_static_array d n vs)) /\
           EVERY (\k. n <= k) (MAP FST (enumerate_static_array d n vs))
Proof
  Induct_on `vs` >>
  simp[enumerate_static_array_def, LET_THM] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (first_x_assum (qspecl_then [`d`, `SUC n`] strip_assume_tac) >>
      simp[] >> irule EVERY_MONOTONIC >>
      qexists_tac `\k. SUC n <= k` >> simp[])
  >> first_x_assum (qspecl_then [`d`, `SUC n`] strip_assume_tac) >>
  simp[sortingTheory.SORTED_DEF] >>
  reverse conj_tac
  >- (irule EVERY_MONOTONIC >>
      qexists_tac `\k. SUC n <= k` >> simp[])
  >> Cases_on `MAP FST (enumerate_static_array d (SUC n) vs)` >> simp[] >>
  gvs[EVERY_DEF]
QED

Theorem enumerate_static_array_sorted[local]:
  !d n vs. SORTED $< (MAP FST (enumerate_static_array d n vs))
Proof
  metis_tac[enumerate_static_array_sorted_aux]
QED

(* enumerate_static_array + all_have_type => sparse_has_type *)
Theorem enumerate_static_array_sparse_has_type[local]:
  !tv vs n.
    all_have_type tv vs ==>
    sparse_has_type tv (n + LENGTH vs)
      (enumerate_static_array (default_value tv) n vs)
Proof
  Induct_on `vs` >>
  simp[enumerate_static_array_def, value_has_type_def, LET_THM] >>
  rpt strip_tac >>
  IF_CASES_TAC >> gvs[value_has_type_def, ADD1]
  >- (first_x_assum $ qspecl_then [`tv`, `SUC n`] mp_tac >> simp[ADD1])
  >> simp[] >>
  first_x_assum $ qspecl_then [`tv`, `SUC n`] mp_tac >> simp[ADD1]
QED

(* decode_static_array returns exactly n elements *)
Theorem decode_static_array_length[local]:
  !storage offset tv n vs.
    decode_static_array storage offset tv n = SOME vs ==>
    LENGTH vs = n
Proof
  Induct_on `n` >>
  simp[Once decode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

(* decode_dyn_array returns exactly n elements *)
Theorem decode_dyn_array_length[local]:
  !storage offset tv n vs.
    decode_dyn_array storage offset tv n = SOME vs ==>
    LENGTH vs = n
Proof
  Induct_on `n` >>
  simp[Once decode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

(* Helper: decode_value produces a well-typed value when tv is well-formed *)
Theorem decode_value_well_typed:
  (!storage offset tv v.
     decode_value storage offset tv = SOME v /\
     well_formed_type_value tv ==> value_has_type tv v) /\
  (!storage offset tvs vs.
     decode_tuple storage offset tvs = SOME vs /\
     EVERY well_formed_type_value tvs ==> values_have_types tvs vs) /\
  (!storage offset tv n vs.
     decode_static_array storage offset tv n = SOME vs /\
     well_formed_type_value tv ==> all_have_type tv vs) /\
  (!storage offset tv n vs.
     decode_dyn_array storage offset tv n = SOME vs /\
     well_formed_type_value tv ==> all_have_type tv vs) /\
  (!storage offset ftypes fields.
     decode_struct storage offset ftypes = SOME fields /\
     EVERY (well_formed_type_value o SND) ftypes ==>
     struct_has_type ftypes fields)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >>
  simp[decode_value_def, AllCaseEqs(), value_has_type_inv,
       well_formed_type_value_def, value_has_type_def, PULL_EXISTS,
       decode_base_from_slot_well_typed] >>
  rpt strip_tac >> gvs[]
  >~[`decode_dyn_bytes _ _ _ = SOME _`]
  >- (metis_tac[decode_dyn_bytes_length])
  >- (metis_tac[decode_dyn_bytes_length])
  >~[`values_have_types _ _`]
  >- (first_x_assum irule >> gvs[EVERY_MEM])
  >~[`SORTED`]
  >- simp[enumerate_static_array_sorted]
  >~[`sparse_has_type`]
  >- (qpat_x_assum `decode_static_array _ _ _ _ = _`
        (ASSUME_TAC o MATCH_MP decode_static_array_length) >>
      gvs[] >>
      irule (enumerate_static_array_sparse_has_type
             |> Q.SPECL [`tv`,`vs`,`0`]
             |> SIMP_RULE (srw_ss()) []) >>
      simp[])
  >~[`decode_dyn_array`]
  >- (qpat_x_assum `decode_dyn_array _ _ _ _ = _`
        (ASSUME_TAC o MATCH_MP decode_dyn_array_length) >>
      gvs[MIN_DEF])
  >~[`struct_has_type`]
  >- (first_x_assum irule >> gvs[EVERY_MEM])
QED

(* Helper: read_storage_slot returns a well-typed value *)
Theorem read_storage_slot_well_typed:
  !cx is_transient slot tv st v st'.
    read_storage_slot cx is_transient slot tv st = (INL v, st') /\
    well_formed_type_value tv ==>
    value_has_type tv v
Proof
  simp[read_storage_slot_def, bind_apply, AllCaseEqs(),
       get_storage_backend_def, return_def, lift_option_def,
       option_CASE_rator, raise_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all (cj 1 decode_value_well_typed) >> simp[]
QED

Theorem switch_BoolV_cases:
  !tv f_true f_false st res st'.
    switch_BoolV tv f_true f_false st = (res, st') ==>
    (tv = Value (BoolV T) /\ f_true st = (res, st')) \/
    (tv = Value (BoolV F) /\ f_false st = (res, st')) \/
    (tv <> Value (BoolV T) /\ tv <> Value (BoolV F) /\
     res = INR (Error (TypeError
       (if is_Value tv then "not BoolV" else "not Value"))) /\
     st' = st)
Proof
  rw[switch_BoolV_def] >> rpt IF_CASES_TAC >> gvs[raise_def]
QED

(* State preservation through switch_BoolV *)
Theorem switch_BoolV_preserves:
  !tv f_true f_false st res st' (P : evaluation_state -> bool).
    switch_BoolV tv f_true f_false st = (res, st') /\
    (!res' st''. f_true st = (res', st'') ==> P st'') /\
    (!res' st''. f_false st = (res', st'') ==> P st'') /\
    P st ==> P st'
Proof
  rw[switch_BoolV_def] >> rpt IF_CASES_TAC >> gvs[raise_def] >> res_tac
QED
Theorem push_scope_swt:
  !st. state_well_typed st ==>
    state_well_typed (st with scopes updated_by CONS FEMPTY)
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_DEF]
QED

(* push_scope preserves env_consistent *)
Theorem push_scope_ec:
  !env cx st.
    env_consistent env cx st ==>
    env_consistent env cx (st with scopes updated_by CONS FEMPTY)
Proof
  rw[env_consistent_def, lookup_scopes_def, FLOOKUP_DEF] >>
  metis_tac[]
QED

(* pop_scope preserves state_well_typed *)
Theorem pop_scope_swt:
  !st h tl. state_well_typed st /\ st.scopes = h::tl ==>
    state_well_typed (st with scopes := tl)
Proof
  rw[state_well_typed_def] >> gvs[]
QED

(* pop_scope preserves env_consistent when the outer env's variables
   are all in the tail scopes (i.e., no env variable was only in head) *)
Theorem pop_scope_ec:
  !env cx st h tl.
    env_consistent env cx st /\ st.scopes = h::tl /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE) ==>
    env_consistent env cx (st with scopes := tl)
Proof
  rw[env_consistent_def] >> rpt strip_tac
  >- (res_tac >> gvs[lookup_scopes_def] >> res_tac)
  >> res_tac
QED

(* new_variable preserves state_well_typed when the added binding is well-typed *)
Theorem new_variable_swt:
  !id tv v st res st'.
    new_variable id tv v st = (res, st') /\
    state_well_typed st /\ value_has_type tv v /\ well_formed_type_value tv ==>
    state_well_typed st'
Proof
  rw[new_variable_def, LET_THM, state_well_typed_def] >>
  gvs[bind_def, ignore_bind_def, get_scopes_def, type_check_def,
      check_def, assert_def, set_scopes_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `st.scopes` >>
  gvs[raise_def, set_scopes_def, return_def,
      scope_well_typed_def, finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
  rw[] >> gvs[] >> res_tac
QED

(* new_variable preserves env_consistent when the id is NOT
   in env.var_types (the common case for local variable declarations) *)
Theorem new_variable_ec:
  !id tv v st res st' env cx.
    new_variable id tv v st = (res, st') /\
    env_consistent env cx st /\
    string_to_num id NOTIN FDOM env.var_types ==>
    env_consistent env cx st'
Proof
  rw[new_variable_def, LET_THM] >>
  gvs[bind_def, ignore_bind_def, get_scopes_def, type_check_def,
      check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `st.scopes` >> gvs[raise_def, set_scopes_def, return_def] >>
  (* Now: env_consistent env cx st, st.scopes = h::t,
     goal: env_consistent env cx (st with scopes := (h |+ ...) :: t) *)
  `!k. k <> string_to_num id ==>
    lookup_scopes k ((h |+ (string_to_num id, <| assignable := T; type := tv; value := v |>)) :: t) =
    lookup_scopes k (h :: t)` by
    (rw[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  rw[env_consistent_def] >> fs[env_consistent_def]
  >- (
    (* var_types *)
    Cases_on `id' = string_to_num id` >- fs[FLOOKUP_DEF] >>
    first_x_assum drule >> strip_tac >>
    res_tac >> gvs[lookup_scopes_def, FLOOKUP_UPDATE])
  (* global_types + toplevel_types: identical *)
  >> res_tac
QED

(* new_variable never produces ReturnException *)
Theorem new_variable_not_return:
  !id tv v st e st'.
    new_variable id tv v st = (INR e, st') ==>
    !w. e <> ReturnException w
Proof
  rw[new_variable_def, LET_THM, bind_def, ignore_bind_def,
     get_scopes_def, type_check_def,
     check_def, assert_def, set_scopes_def, return_def, raise_def,
     lookup_scopes_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[raise_def, set_scopes_def, return_def]
QED
Theorem bind_state_preserving:
  !f g st res st'.
    (!st0 r0 st0'. f st0 = (r0, st0') ==> st0' = st0) /\
    (!v st0 r0 st0'. g v st0 = (r0, st0') ==> st0' = st0) /\
    bind f g st = (res, st') ==> st' = st
Proof
  rw[bind_def, AllCaseEqs()] >> res_tac >> gvs[]
QED
Theorem subscript_pure_ops_state:
  !tv st_e res st'.
    (do v <- get_Value tv;
        k <- lift_option_type (value_to_key v) s;
        return (loc, k::sbs)
     od) st_e = (res, st') ==>
    st' = st_e
Proof
  Cases_on `tv` >>
  simp[bind_def, get_Value_def, lift_option_type_def, return_def, raise_def] >>
  rpt CASE_TAC >> fs[return_def, raise_def]
QED


(* ===== P7 cases ===== *)
(*
  Helper: connect get_immutables success to immutables well-typedness.
  If get_immutables succeeds with result imms, and FLOOKUP imms id = SOME (tv,v),
  then imms_well_typed gives value_has_type tv v.
*)
Theorem immutables_lookup_well_typed:
  !cx src st imms id tv v.
    get_immutables cx src st = (INL imms, st) /\
    FLOOKUP imms id = SOME (tv, v) /\
    state_well_typed st ==>
    value_has_type tv v
Proof
  rw[] >> imp_res_tac get_immutables_SOME >> gvs[] >>
  fs[state_well_typed_def, get_source_immutables_def] >>
  Cases_on `ALOOKUP mods src` >> gvs[FLOOKUP_DEF] >>
  rename1 `ALOOKUP mods _ = SOME src_imm` >>
  qpat_x_assum `ALOOKUP st.immutables _ = _`
    (strip_assume_tac o MATCH_MP (DB.fetch "alist" "ALOOKUP_MEM")) >>
  fs[EVERY_MEM, FORALL_PROD] >>
  first_x_assum drule >> simp[imms_well_typed_def] >>
  disch_then (qspecl_then [`src`, `src_imm`, `id`, `tv`, `v`] mp_tac) >>
  simp[FLOOKUP_DEF]
QED

(*
  Helper: connect get_immutables success to env_consistent's immutables condition.
  The env_consistent global_types clause quantifies over
  get_source_immutables (current_module cx) (case ALOOKUP st.immutables ...).
  When get_immutables cx (current_module cx) st succeeds with imms,
  imms IS that get_source_immutables result.
*)
Theorem get_immutables_env_consistent_link:
  !cx src st imms.
    get_immutables cx src st = (INL imms, st) ==>
    imms = get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m)
Proof
  rw[] >> imp_res_tac get_immutables_SOME >> gvs[]
QED


(* ===== Scope bracket helpers: push + eval_stmts + pop ===== *)

(* After pushing a scope, running eval_stmts, and popping, env_consistent
   is restored. The IH gives env_consistent on st_body; popping the head
   scope preserves it because:
   - var_types: variables in tail are found by lookup_scopes in both
     st_body.scopes and TL st_body.scopes (new head entries aren't in tail)
   - global_types/type_defs/fn_sigs: unchanged by pop_scope *)
Theorem scope_bracket_preserves_ec:
  !env cx st sc ss res st_body.
    env_consistent env cx st_body /\
    eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
    (!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc) ==>
    env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac >>
  imp_res_tac eval_stmts_new_in_head_not_in_tail >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  fs[env_consistent_def] >> rpt strip_tac
  (* var_types clause *)
  >- (
    Cases_on `FLOOKUP (HD st_body.scopes) id`
    (* id not in head: lookup in full scopes = lookup in tail *)
    >- (res_tac >> Cases_on `st_body.scopes` >> gvs[lookup_scopes_def] >> res_tac)
    (* id in head of st_body *)
    >> `id IN FDOM (HD st_body.scopes)` by gvs[FLOOKUP_DEF] >>
    (* id not in pushed head sc (by disjointness with env.var_types) *)
    `id NOTIN FDOM sc` by
      (first_x_assum irule >> gvs[FLOOKUP_DEF]) >>
    `id NOTIN FDOM (HD ((st with scopes updated_by CONS sc).scopes))` by
      simp[] >>
    (* id is new in head: new_in_head gives contradiction *)
    `(st with scopes updated_by CONS sc).scopes <> []` by simp[] >>
    res_tac >> gvs[])
  (* global_types clause: immutables unchanged by pop *)
  >> res_tac
QED

(* After pushing a scope and running eval_stmts, popping preserves
   state_well_typed (assuming the body state is well-typed). *)
Theorem scope_bracket_preserves_swt:
  !st sc ss cx res st_body.
    eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
    state_well_typed st_body ==>
    state_well_typed (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `st_body.scopes` >> gvs[] >>
  irule pop_scope_swt >> metis_tac[]
QED


(* push_scope_with_var preserves state_well_typed when binding is well-typed *)
Theorem push_scope_with_var_swt:
  !nm tv v st.
    state_well_typed st /\ value_has_type tv v /\ well_formed_type_value tv ==>
    state_well_typed (st with scopes updated_by CONS (FEMPTY |+ (nm, <| assignable := F; type := tv; value := v |>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

(* push_scope_with_var gives env_consistent for the extended env *)
Theorem push_scope_with_var_ec:
  !env cx st nm typ tyv v.
    env_consistent env cx st /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    nm NOTIN FDOM env.var_types ==>
    env_consistent (env with var_types updated_by flip FUPDATE (nm, typ)) cx
      (st with scopes updated_by CONS (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)))
Proof
  rw[env_consistent_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `id = nm` >> gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  res_tac
QED


(* env_consistent weakening: if it holds for an env with more var_types,
   it holds for one with fewer (since the implication has a weaker antecedent) *)
Theorem env_consistent_weaken_var_types:
  !env env' cx st.
    env_consistent env' cx st /\
    env.type_defs = env'.type_defs /\
    env.fn_sigs = env'.fn_sigs /\
    env.global_types = env'.global_types /\
    env.toplevel_types = env'.toplevel_types /\
    env.flag_members = env'.flag_members /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
             FLOOKUP env'.var_types id = SOME ty) ==>
    env_consistent env cx st
Proof
  rw[env_consistent_def] >> res_tac
QED

(* Common special case: removing one FUPDATE from var_types *)
Theorem env_consistent_drop_var:
  !env nm typ cx st.
    env_consistent (env with var_types updated_by flip FUPDATE (nm, typ)) cx st /\
    nm NOTIN FDOM env.var_types ==>
    env_consistent env cx st
Proof
  rpt strip_tac >> irule env_consistent_weaken_var_types >>
  qexists_tac `env with var_types updated_by flip FUPDATE (nm, typ)` >>
  simp[FLOOKUP_UPDATE] >> rw[] >>
  gvs[FLOOKUP_DEF]
QED


(* struct_has_type lookup: if a field is in the struct, its type is in ftypes *)
Theorem struct_has_type_lookup:
  !ftypes fields id v.
    struct_has_type ftypes fields /\ ALOOKUP fields id = SOME v ==>
    ?tv. ALOOKUP ftypes id = SOME tv /\ value_has_type tv v
Proof
  Induct >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def] >>
  rpt gen_tac >> Cases_on `fields` >> simp[value_has_type_def] >>
  Cases_on `h` >> simp[value_has_type_def] >>
  rw[] >> metis_tac[]
QED

(* evaluate_attribute preserves typing *)
Theorem evaluate_attribute_well_typed:
  !sv id v ftypes.
    evaluate_attribute sv id = INL v /\
    value_has_type (StructTV ftypes) sv ==>
    ?tv. ALOOKUP ftypes id = SOME tv /\ value_has_type tv v
Proof
  Cases >> simp[evaluate_attribute_def, value_has_type_inv] >>
  rw[] >> gvs[AllCaseEqs()] >>
  metis_tac[struct_has_type_lookup]
QED

(* Helper: OPT_MMAP + ALOOKUP on ZIP *)
Theorem OPT_MMAP_ALOOKUP_ZIP:
  !f (args:('k # 'a) list) ys field_id ty.
    OPT_MMAP f (MAP SND args) = SOME ys /\
    ALOOKUP args field_id = SOME ty ==>
    ?tv. f ty = SOME tv /\
         ALOOKUP (ZIP(MAP FST args, ys)) field_id = SOME tv
Proof
  Induct_on `args` >> simp[] >>
  Cases >> simp[OPT_MMAP_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `q = field_id` >> gvs[]
QED

(* attribute_type_ok + evaluate_type gives ALOOKUP on ftypes *)
Theorem attribute_type_evaluates:
  !tenv struct_ty field_id result_ty ftypes.
    attribute_type_ok tenv struct_ty field_id result_ty /\
    evaluate_type tenv struct_ty = SOME (StructTV ftypes) ==>
    ?tv. evaluate_type tenv result_ty = SOME tv /\
         ALOOKUP ftypes field_id = SOME tv
Proof
  Cases_on `struct_ty` >> simp[attribute_type_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM, evaluate_types_OPT_MMAP] >>
  Cases_on `ALOOKUP args field_id` >> gvs[] >>
  drule_all OPT_MMAP_ALOOKUP_ZIP >> strip_tac >>
  metis_tac[evaluate_type_mono]
QED

(* ===== Unconditional env_consistent preservation ===== *)
(* eval_expr/eval_exprs preserve env_consistent without typing hypotheses,
   because env_consistent only tracks type tags (not values). *)

val ec_unconditional_tac =
  rpt strip_tac >>
  irule env_consistent_preserves_tv >>
  qexists_tac `st` >> simp[] >>
  imp_res_tac (cj 8 eval_preserves_tv) >>
  imp_res_tac (cj 9 eval_preserves_tv) >>
  TRY (imp_res_tac eval_expr_preserves_scopes_dom) >>
  TRY (imp_res_tac eval_exprs_preserves_scopes_dom) >>
  TRY (imp_res_tac eval_expr_preserves_immutables_addr_dom) >>
  TRY (imp_res_tac eval_exprs_preserves_immutables_addr_dom) >>
  TRY (imp_res_tac eval_expr_preserves_immutables_dom) >>
  TRY (imp_res_tac eval_exprs_preserves_immutables_dom) >>
  simp[] >>
  rpt strip_tac >>
  `(IS_SOME (ALOOKUP st.immutables cx.txn.target) <=>
    IS_SOME (ALOOKUP st'.immutables cx.txn.target))` by simp[] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
  gvs[] >>
  res_tac >> gvs[];

Theorem eval_expr_preserves_ec:
  !cx e st res st' env.
    env_consistent env cx st /\
    eval_expr cx e st = (res, st') ==>
    env_consistent env cx st'
Proof
  ec_unconditional_tac
QED

Theorem eval_exprs_preserves_ec:
  !cx es st res st' env.
    env_consistent env cx st /\
    eval_exprs cx es st = (res, st') ==>
    env_consistent env cx st'
Proof
  ec_unconditional_tac
QED

(* Evaluation with modified stk preserves ec for original cx.
   Key insight: preserves_tv only depends on cx.txn.target,
   and stk update doesn't change txn. *)
local
  (* Helper: preserves_tv (cx with stk updated_by f) = preserves_tv cx *)
  val preserves_tv_stk = prove(
    ``preserves_tv (cx with stk updated_by f) st st' =
      preserves_tv cx st st'``,
    SRW_TAC[][preserves_tv_def]);

  fun ec_stk_tac ptv_cj scopes_dom_thm imms_addr_thm imms_dom_thm =
    rpt strip_tac >>
    imp_res_tac (ptv_cj eval_preserves_tv) >>
    RULE_ASSUM_TAC (REWRITE_RULE [preserves_tv_stk]) >>
    irule env_consistent_preserves_tv >>
    qexists_tac `st` >> simp[] >>
    imp_res_tac scopes_dom_thm >> simp[] >>
    rpt strip_tac >>
    imp_res_tac imms_addr_thm >>
    imp_res_tac imms_dom_thm >>
    `(IS_SOME (ALOOKUP st.immutables cx.txn.target) <=>
      IS_SOME (ALOOKUP st'.immutables cx.txn.target))` by simp[] >>
    Cases_on `ALOOKUP st.immutables cx.txn.target` >>
    Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
    gvs[] >> res_tac >> gvs[]
in

Theorem eval_expr_preserves_ec_stk:
  !cx f e st res st' env.
    env_consistent env cx st /\
    eval_expr (cx with stk updated_by f) e st = (res, st') ==>
    env_consistent env cx st'
Proof
  ec_stk_tac (cj 8) eval_expr_preserves_scopes_dom
    eval_expr_preserves_immutables_addr_dom eval_expr_preserves_immutables_dom
QED

Theorem eval_exprs_preserves_ec_stk:
  !cx f es st res st' env.
    env_consistent env cx st /\
    eval_exprs (cx with stk updated_by f) es st = (res, st') ==>
    env_consistent env cx st'
Proof
  ec_stk_tac (cj 9) eval_exprs_preserves_scopes_dom
    eval_exprs_preserves_immutables_addr_dom eval_exprs_preserves_immutables_dom
QED

end (* local *)

(* ===== StructLit value typing ===== *)

(* struct_has_type with same field names reduces to pointwise value_has_type *)
Theorem struct_has_type_zip_same_names:
  !names tvs vs.
    LENGTH names = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\
    LIST_REL value_has_type tvs vs ==>
    struct_has_type (ZIP (names, tvs)) (ZIP (names, vs))
Proof
  Induct >> simp[Once value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >> Cases_on `vs` >> gvs[Once value_has_type_def]
QED

(* OPT_MMAP on a restricted tenv gives the same result via evaluate_type_mono *)
Theorem OPT_MMAP_evaluate_type_mono:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac evaluate_type_mono >> simp[] >>
  first_x_assum (qspecl_then [`tenv`, `nid`] mp_tac) >> simp[]
QED

Theorem OPT_MMAP_LENGTH:
  !f xs ys. OPT_MMAP f xs = SOME ys ==> LENGTH ys = LENGTH xs
Proof
  Induct_on `xs` >> simp[OPT_MMAP_def] >>
  rpt gen_tac >> Cases_on `f h` >> simp[] >>
  Cases_on `OPT_MMAP f xs` >> simp[] >>
  strip_tac >> gvs[] >> res_tac
QED

(* ===== Subscript value typing ===== *)

(* Helper: materialise of Value is always return *)
Theorem materialise_Value[simp]:
  !cx v st. materialise cx (Value v) st = (INL v, st)
Proof
  simp[materialise_def, return_def]
QED

(* ===== Subscript helpers ===== *)

(* For the direct-value branch of evaluate_subscript:
   If subscript_type_ok holds and the container is well-typed,
   array_index returns a well-typed element. *)
Theorem evaluate_subscript_value_well_typed:
  !tenv arr_tv av idx v ct it ty rtv.
    subscript_type_ok ct it ty /\
    evaluate_type tenv ct = SOME arr_tv /\
    evaluate_type tenv ty = SOME rtv /\
    value_has_type arr_tv (ArrayV av) /\
    array_index arr_tv av idx = SOME v ==>
    value_has_type rtv v
Proof
  rpt gen_tac >>
  Cases_on `ct` >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[]
  (* TupleT case: EVERY ($= ty) l, l <> [] *)
  >- (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
      Cases_on `av` >> gvs[value_has_type_inv] >>
      gvs[array_index_def, AllCaseEqs()] >>
      gvs[oEL_EQ_EL] >>
      gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
      first_x_assum (qspec_then `Num idx` mp_tac) >> simp[EL_MAP] >>
      `EL (Num idx) l = ty` by (gvs[EVERY_EL] >> res_tac) >>
      gvs[])
  (* ArrayT case: result_ty = elem_ty *)
  >> (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      imp_res_tac (cj 1 evaluate_type_well_formed) >>
      drule_all array_index_well_typed >> simp[])
QED


(* evaluate_subscripts preserves value typing relative to leaf_type *)
(* evaluate_subscripts preserves value typing relative to leaf_type.
   Precondition: leaf_type tv subs <> NoneTV — this excludes TupleTV
   (where leaf_type gives NoneTV but the actual element type differs). *)
Theorem evaluate_subscripts_well_typed:
  !subs tv a v.
    evaluate_subscripts tv a subs = INL v /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV ==>
    value_has_type (leaf_type tv subs) v /\
    well_formed_type_value (leaf_type tv subs)
Proof
  Induct >> simp[evaluate_subscripts_def, leaf_type_def] >>
  gen_tac >> Cases_on `h` >>
  simp[evaluate_subscripts_def, leaf_type_def] >>
  rpt gen_tac >> strip_tac
  (* IntSubscript: array index *)
  >- (
    Cases_on `a` >>
    gvs[evaluate_subscripts_def, AllCaseEqs()] >>
    (* leaf_type tv (IntSubscript::subs) <> NoneTV forces tv = ArrayTV *)
    `?elem_tv bd. tv = ArrayTV elem_tv bd` by
      (Cases_on `tv` >> gvs[leaf_type_def]) >>
    gvs[leaf_type_def, well_formed_type_value_def] >>
    drule_all array_index_well_typed >> strip_tac >>
    first_x_assum drule_all >> simp[])
  (* AttrSubscript: struct field lookup *)
  >> (
    Cases_on `a` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
    (* leaf_type tv (AttrSubscript::subs) <> NoneTV forces tv = StructTV *)
    Cases_on `tv` >>
    gvs[evaluate_subscripts_def, leaf_type_def, AllCaseEqs(), value_has_type_def] >>
    rename1 `StructTV ftypes` >>
    Cases_on `ALOOKUP ftypes s` >> gvs[] >>
    rename1 `ALOOKUP ftypes s = SOME ftv` >>
    (* struct_has_type ftypes l, ALOOKUP l s = SOME fv *)
    `value_has_type ftv v'` by
      (drule struct_has_type_lookup >>
       disch_then drule >> strip_tac >> gvs[]) >>
    `well_formed_type_value ftv` by
      (gvs[well_formed_type_value_def, EVERY_MEM, MEM_MAP] >>
       drule alistTheory.ALOOKUP_MEM >> strip_tac >>
       first_x_assum (qspec_then `(s, ftv)` mp_tac) >> simp[]) >>
    first_x_assum drule_all >> simp[])
QED

(* popped_value on a well-typed DynArray returns a well-typed element *)
Theorem popped_value_well_typed:
  !arr v elem_tv m.
    popped_value arr = INL v /\
    value_has_type (ArrayTV elem_tv (Dynamic m)) arr ==>
    value_has_type elem_tv v
Proof
  Cases >> simp[popped_value_def, value_has_type_inv] >>
  Cases_on `a` >> simp[popped_value_def, value_has_type_inv] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `MEM (LAST l) l` by (irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  gvs[all_have_type_EVERY, EVERY_MEM]
QED

(* assign_result PopOp returns a well-typed value.
   Precondition: leaf_type tv subs is ArrayTV (not NoneTV/TupleTV).
   This is satisfied when the target has array type. *)
Theorem assign_result_pop_well_typed:
  !tv a subs v st st'.
    assign_result tv PopOp a subs st = (INL (SOME v), st') /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV ==>
    ?elem_tv bd.
      leaf_type tv subs = ArrayTV elem_tv bd /\
      value_has_type elem_tv v
Proof
  rpt gen_tac >> strip_tac >>
  gvs[assign_result_def, bind_apply, lift_sum_def, AllCaseEqs(), return_def] >>
  (* Extract: evaluate_subscripts tv a subs = INL arr *)
  Cases_on `evaluate_subscripts tv a subs` >> gvs[return_def, raise_def] >>
  (* Extract: popped_value arr = INL v *)
  Cases_on `popped_value arr` >> gvs[return_def, raise_def] >>
  (* Apply evaluate_subscripts_well_typed *)
  `value_has_type (leaf_type tv subs) arr /\
   well_formed_type_value (leaf_type tv subs)` by
    (irule evaluate_subscripts_well_typed >> metis_tac[]) >>
  (* popped_value arr = INL v implies arr = ArrayV (DynArrayV vs),
     so value_has_type (leaf_type tv subs) arr forces ArrayTV form *)
  `?vs. arr = ArrayV (DynArrayV vs) /\ vs <> []` by (
    Cases_on `arr` >> gvs[popped_value_def] >>
    Cases_on `a'` >> gvs[popped_value_def] >>
    CASE_TAC >> gvs[]) >>
  gvs[value_has_type_inv, popped_value_def, all_have_type_EVERY,
      EVERY_MEM, MEM_LAST_NOT_NIL]
QED

(* ===== toplevel_value well-formedness ===== *)
(* Invariant: eval_expr returns toplevel_values whose embedded
   type_values are well-formed. Needed for Subscript case of
   type_preservation (materialise of ArrayRef needs wfty for
   read_storage_slot_well_typed). *)

(* toplevel_value_typed + materialise success => value_has_type *)
Theorem toplevel_value_typed_materialise:
  !cx tv tyv st v st'.
    toplevel_value_typed tv tyv /\
    toplevel_value_wf tv /\
    materialise cx tv st = (INL v, st') ==>
    value_has_type tyv v
Proof
  rpt gen_tac >> Cases_on `tv` >>
  simp[toplevel_value_typed_def, materialise_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[bind_def, UNCURRY, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[read_storage_slot_well_typed]
QED

Theorem toplevel_value_typed_not_HashMapRef:
  !x tyv. toplevel_value_typed x tyv /\ tyv <> NoneTV ==> ~is_HashMapRef x
Proof
  Cases >> simp[is_HashMapRef_def, toplevel_value_typed_def]
QED

(* ===== env_consistent toplevel clause extraction ===== *)
(* Reusable lemmas for TopLevelName, BareGlobalName, etc. *)

Theorem env_consistent_toplevel_storage:
  !env cx st src id ty ts is_transient typ id_str.
    env_consistent env cx st /\
    FLOOKUP env.toplevel_types (src, id) = SOME ty /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ, id_str) ==>
    typ = ty
Proof
  rpt strip_tac >> gvs[env_consistent_def] >>
  first_x_assum (qspecl_then [`src`, `id`, `ty`, `ts`] mp_tac) >> gvs[]
QED

Theorem env_consistent_toplevel_hashmap:
  !env cx st src id ty ts is_transient kt vt id_str.
    env_consistent env cx st /\
    FLOOKUP env.toplevel_types (src, id) = SOME ty /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
    ty = NoneT
Proof
  rpt strip_tac >> gvs[env_consistent_def] >>
  first_x_assum (qspecl_then [`src`, `id`, `ty`, `ts`] mp_tac) >> gvs[]
QED

Theorem env_consistent_toplevel_immutable:
  !env cx st src id ty ts tv v.
    env_consistent env cx st /\
    FLOOKUP env.toplevel_types (src, id) = SOME ty /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num id ts = NONE /\
    FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of
         NONE => [] | SOME m => m)) id = SOME (tv, v) ==>
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rpt strip_tac >> gvs[env_consistent_def] >>
  first_x_assum (qspecl_then [`src`, `id`, `ty`, `ts`] mp_tac) >> gvs[]
QED

(* lookup_global returns HashMapRef only for HashMapVarDecl *)
Theorem lookup_global_HashMapRef[local]:
  !cx src n st is_t bs kt vt st'.
    lookup_global cx src n st = (INL (HashMapRef is_t bs kt vt), st') ==>
    ?ts id_str. get_module_code cx src = SOME ts /\
                find_var_decl_by_num n ts = SOME (HashMapVarDecl is_t kt vt, id_str)
Proof
  rpt strip_tac >>
  imp_res_tac lookup_global_state >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [lookup_global_def, bind_def, return_def, raise_def,
    lift_option_type_def, ignore_bind_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[]
  >- (Cases_on `get_immutables cx src st` >> Cases_on `q` >>
      gvs[bind_def, raise_def, return_def] >>
      Cases_on `FLOOKUP x' n` >> gvs[raise_def, return_def] >>
      Cases_on `x''` >> gvs[return_def])
  >> Cases_on `x'` >> Cases_on `q` >> gvs[]
  >- (
    (* StorageVarDecl: never produces HashMapRef *)
    simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
    CASE_TAC >> simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    CASE_TAC >> simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    CASE_TAC >> simp_tac (srw_ss()) [return_def, raise_def, bind_def, UNCURRY] >>
    rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, UNCURRY]))
  >> (* HashMapVarDecl *)
  simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx b src r` >>
  simp_tac (srw_ss()) [return_def, raise_def, bind_def]
QED

(* lookup_global returning ArrayRef implies StorageVarDecl + evaluate_type = ArrayTV *)
Theorem lookup_global_ArrayRef[local]:
  !cx src n st is_t bs etv ebd st'.
    lookup_global cx src n st = (INL (ArrayRef is_t bs etv ebd), st') ==>
    ?ts id_str typ. get_module_code cx src = SOME ts /\
                    find_var_decl_by_num n ts = SOME (StorageVarDecl is_t typ, id_str) /\
                    evaluate_type (get_tenv cx) typ = SOME (ArrayTV etv ebd)
Proof
  rpt strip_tac >>
  imp_res_tac lookup_global_state >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [lookup_global_def, bind_def, return_def, raise_def,
    lift_option_type_def, ignore_bind_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[]
  >- (Cases_on `get_immutables cx src st` >> Cases_on `q` >>
      gvs[bind_def, raise_def, return_def] >>
      Cases_on `FLOOKUP x' n` >> gvs[raise_def, return_def] >>
      Cases_on `x''` >> gvs[return_def])
  >> Cases_on `x'` >> Cases_on `q` >> gvs[]
  >- (
    (* StorageVarDecl: evaluate_type gives ArrayTV → ArrayRef *)
    simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
    CASE_TAC >> simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    CASE_TAC >> simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    CASE_TAC >> simp_tac (srw_ss()) [return_def, raise_def, bind_def, UNCURRY] >>
    rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, UNCURRY]))
  >> (* HashMapVarDecl: never produces ArrayRef *)
  simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx b src r` >>
  simp_tac (srw_ss()) [return_def, raise_def, bind_def]
QED

(* ===== lookup_global produces toplevel_value_typed ===== *)
Theorem lookup_global_toplevel_typed:
  !cx src n st tv st' env ty tyv.
    lookup_global cx src n st = (INL tv, st') /\
    FLOOKUP env.toplevel_types (src, n) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    env_consistent env cx st /\ state_well_typed st ==>
    toplevel_value_typed tv tyv
Proof
  rpt strip_tac >>
  imp_res_tac lookup_global_state >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [lookup_global_def, bind_def, return_def, raise_def,
    lift_option_type_def, ignore_bind_def] >>
  Cases_on `get_module_code cx src`
  >- gvs[return_def, raise_def, bind_def]
  >> gvs[return_def, bind_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[]
  >- (
    Cases_on `get_immutables cx src st` >> Cases_on `q` >>
    gvs[bind_def, raise_def, return_def] >>
    Cases_on `FLOOKUP x' n` >> gvs[raise_def, return_def] >>
    Cases_on `x''` >> strip_tac >> gvs[return_def, toplevel_value_typed_def] >>
    imp_res_tac get_immutables_state >> rpt BasicProvers.VAR_EQ_TAC >>
    drule get_immutables_well_typed >> disch_then drule >> strip_tac >>
    drule get_immutables_env_consistent_link >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    drule_all env_consistent_toplevel_immutable >> strip_tac >>
    gvs[] >> metis_tac[]
  ) >>
  Cases_on `x'` >> Cases_on `q` >> gvs[]
  >- (
    drule_all env_consistent_toplevel_storage >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
    Cases_on `lookup_var_slot_from_layout cx b src r` >>
    simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    imp_res_tac (cj 1 evaluate_type_well_formed) >>
    Cases_on `tyv` >>
    simp_tac (srw_ss()) [bind_def, return_def, raise_def,
                         toplevel_value_typed_def, UNCURRY] >>
    rpt strip_tac >>
    gvs[pairTheory.pair_case_eq, CaseEq"sum",
        return_def, raise_def, toplevel_value_typed_def,
        bind_def, UNCURRY] >>
    metis_tac[read_storage_slot_well_typed]
  )
  >> simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx b src r` >>
  simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
  strip_tac >> gvs[toplevel_value_typed_def] >>
  drule_all env_consistent_toplevel_hashmap >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  gvs[evaluate_type_def]
QED

(* lookup_global + materialise produces well-typed value. *)
Theorem lookup_global_materialise_well_typed:
  !cx src n st tv st' v st'' env ty.
    lookup_global cx src n st = (INL tv, st') /\
    materialise cx tv st' = (INL v, st'') /\
    FLOOKUP env.toplevel_types (src, n) = SOME ty /\
    env_consistent env cx st /\ state_well_typed st ==>
    ?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\ value_has_type tyv v
Proof
  rpt strip_tac >>
  imp_res_tac lookup_global_state >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [lookup_global_def, bind_def, return_def, raise_def,
    lift_option_type_def, ignore_bind_def] >>
  Cases_on `get_module_code cx src`
  >- gvs[return_def, raise_def, bind_def]
  >> gvs[return_def, bind_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[]
  >- (
    Cases_on `get_immutables cx src st` >> Cases_on `q` >>
    gvs[bind_def, raise_def, return_def] >>
    Cases_on `FLOOKUP x' n` >> gvs[raise_def, return_def] >>
    Cases_on `x''` >> strip_tac >> gvs[return_def, materialise_def] >>
    imp_res_tac get_immutables_state >> rpt BasicProvers.VAR_EQ_TAC >>
    drule get_immutables_well_typed >> disch_then drule >> strip_tac >>
    drule get_immutables_env_consistent_link >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    drule_all env_consistent_toplevel_immutable >> strip_tac >>
    gvs[] >> metis_tac[]
  ) >>
  Cases_on `x'` >> Cases_on `q` >> gvs[]
  >- (
    drule_all env_consistent_toplevel_storage >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
    Cases_on `lookup_var_slot_from_layout cx b src r` >>
    simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    Cases_on `evaluate_type (get_tenv cx) t` >>
    simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
    rename [`evaluate_type _ _ = SOME tv_val`] >>
    imp_res_tac (cj 1 evaluate_type_well_formed) >>
    Cases_on `tv_val` >>
    simp_tac (srw_ss()) [bind_def, return_def, raise_def, materialise_def] >>
    rpt strip_tac >>
    gvs[pairTheory.pair_case_eq, CaseEq"sum",
        return_def, raise_def, materialise_def, bind_def] >>
    metis_tac[read_storage_slot_well_typed]
  )
  >> simp_tac (srw_ss()) [bind_def, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx b src r` >>
  simp_tac (srw_ss()) [return_def, raise_def, bind_def] >>
  strip_tac >> gvs[materialise_def, raise_def]
QED

(* resolve_array_element preserves leaf_type *)
(* Combined resolve_array_element properties — single induction for all. *)
Theorem resolve_array_element_props[local]:
  !cx b base tv subs st.
    !slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st = (INL (slot, final_tv, rsubs), st') ==>
    leaf_type tv subs = leaf_type final_tv rsubs /\
    (!etv ebd. final_tv = ArrayTV etv ebd ==> rsubs = []) /\
    (well_formed_type_value tv ==> well_formed_type_value final_tv)
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [Once resolve_array_element_def, bind_apply, return_def,
    raise_def, ignore_bind_apply, BETA_THM] >>
  TRY (strip_tac >> gvs[leaf_type_def, well_formed_type_value_def] >> NO_TAC) >>
  (* Only remaining: ArrayTV + IntSubscript recursive case *)
  Cases_on `bd` >>
  simp_tac (srw_ss()) [bind_apply, return_def, raise_def, check_def,
    get_storage_backend_def, ignore_bind_apply, assert_def,
    AllCaseEqs(), PULL_EXISTS, LET_THM] >>
  rpt (COND_CASES_TAC >> simp_tac (srw_ss()) [return_def, raise_def]) >>
  strip_tac
  >- ( (* Fixed: elem_offset = 0 *)
    first_x_assum (qspecl_then [`base' + n2w (Num idx * type_slot_size tv)`,
                                `0`] mp_tac) >>
    simp[] >> disch_then drule >> strip_tac >>
    gvs[leaf_type_def, well_formed_type_value_def]
  )
  >> ( (* Dynamic: elem_offset = 1 *)
    rpt gen_tac >> strip_tac >>
    first_x_assum (qspecl_then [`base' + n2w (1 + Num idx * type_slot_size tv)`,
                                `1`] mp_tac) >>
    impl_tac >- simp[arithmeticTheory.ADD_COMM] >>
    disch_then drule >> strip_tac >>
    gvs[leaf_type_def, well_formed_type_value_def]
  )
QED

(* assign_target with PopOp returns a well-typed popped value.
   Combines eval_base_target_type_connection + assign_result_pop_well_typed
   for ScopedVar/ImmutableVar, and direct analysis for TopLevelVar. *)
Theorem assign_target_pop_value_well_typed:
  !b cx bt env st0 loc sbs st1 st st' v ty bd.
    eval_base_target cx bt st0 = (INL (loc, sbs), st1) /\
    assign_target cx (BaseTargetV loc sbs) PopOp st = (INL (SOME v), st') /\
    well_typed_target env bt (ArrayT ty bd) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx ==>
    ?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\
          value_has_type tyv v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc`
  >- suspend "ScopedVar"
  >- suspend "ImmutableVar"
  >> suspend "TopLevelVar"
QED

Resume assign_target_pop_value_well_typed[TopLevelVar]:
  (* Get FLOOKUP env.toplevel_types *)
  drule_all eval_base_target_toplevel_flookup >> strip_tac >>
  (* Unfold assign_target for TopLevelVar *)
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [assign_target_def, bind_def, UNCURRY, LET_THM,
    return_def, lift_option_def, lift_option_type_def,
    raise_def, lift_sum_def, ignore_bind_def] >>
  (* lookup_global + get_module_code *)
  Cases_on `lookup_global cx o' (string_to_num s) st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def] >>
  Cases_on `get_module_code cx o'` >>
  ASM_SIMP_TAC (srw_ss()) [return_def, raise_def] >>
  rename1 `get_module_code cx o' = SOME ts` >>
  Cases_on `x` >> simp_tac (srw_ss()) []
  >- suspend "TLV_Value"
  >- suspend "TLV_HashMapRef"
  >> suspend "TLV_ArrayRef"
QED

Resume assign_target_pop_value_well_typed[TLV_Value]:
  rename1 `lookup_global _ _ _ _ = (INL (Value lv), lg_st)` >>
  Cases_on `OPTION_BIND (find_var_decl_by_num (string_to_num s) ts)
              (\p. case FST p of StorageVarDecl _ typ =>
                     evaluate_type (get_tenv cx) typ | _ => NONE)` >>
  ASM_SIMP_TAC (srw_ss()) [return_def, raise_def, bind_apply] >>
  rename1 `OPTION_BIND _ _ = SOME var_tv` >>
  Cases_on `assign_subscripts var_tv lv (REVERSE sbs) PopOp` >>
  ASM_SIMP_TAC (srw_ss()) [return_def, raise_def] >>
  Cases_on `set_global cx o' (string_to_num s) x lg_st` >>
  reverse (Cases_on `q`) >> ASM_SIMP_TAC (srw_ss()) [return_def, raise_def] >>
  strip_tac >>
  (* evaluate_type base_ty = SOME var_tv *)
  (* Decompose OPTION_BIND into find_var_decl + evaluate_type *)
  qpat_x_assum `OPTION_BIND _ _ = SOME _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [OPTION_BIND_EQUALS_OPTION]) >>
  rename1 `find_var_decl_by_num _ _ = SOME vd_pair` >>
  PairCases_on `vd_pair` >>
  gvs[] >>
  Cases_on `vd_pair0` >> gvs[] >>
  (* Now: evaluate_type typ = SOME var_tv, env_consistent gives typ = base_ty *)
  drule_all env_consistent_toplevel_storage >> strip_tac >> gvs[] >>
  (* type connection *)
  drule eval_base_target_type_connection_toplevel >>
  rpt (disch_then drule) >> strip_tac >>
  (* lookup_global_toplevel_typed gives value_has_type var_tv lv *)
  drule_all lookup_global_toplevel_typed >>
  simp[toplevel_value_typed_def] >> strip_tac >>
  (* leaf_type <> NoneTV *)
  `leaf_type var_tv (REVERSE sbs) <> NoneTV` by (
    CCONTR_TAC >> gvs[evaluate_type_def, AllCaseEqs(), LET_THM]) >>
  imp_res_tac assign_result_pop_well_typed >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM]
QED

Resume assign_target_pop_value_well_typed[TLV_HashMapRef]:
  (* HashMapRef: env_consistent forces base_ty = NoneT, giving NoneTV.
     eval_base_target_type_connection_toplevel then requires
     evaluate_type (ArrayT ty bd) = SOME NoneTV, which is impossible. *)
  rename1 `lookup_global _ _ _ _ = (INL (HashMapRef is_t bs kt vt), _)` >>
  imp_res_tac lookup_global_HashMapRef >>
  drule_all env_consistent_toplevel_hashmap >> strip_tac >>
  gvs[] >>
  `evaluate_type (get_tenv cx) NoneT = SOME NoneTV` by simp[evaluate_type_def] >>
  drule eval_base_target_type_connection_toplevel >>
  rpt (disch_then drule) >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM, leaf_type_def]
QED

Resume assign_target_pop_value_well_typed[TLV_ArrayRef]:
  (* Extract facts from lookup_global = ArrayRef *)
  imp_res_tac lookup_global_ArrayRef >>
  drule_all eval_base_target_toplevel_flookup >> strip_tac >>
  drule_all env_consistent_toplevel_storage >> strip_tac >> gvs[] >>
  drule eval_base_target_type_connection_toplevel >>
  rpt (disch_then drule) >> strip_tac >>
  imp_res_tac (cj 1 evaluate_type_well_formed) >>
  simp_tac std_ss [bind_def, UNCURRY, BETA_THM] >>
  Cases_on `resolve_array_element cx b c (ArrayTV t b0) (REVERSE sbs) r` >>
  reverse (Cases_on `q`) >- (
    ASM_SIMP_TAC (srw_ss()) [raise_def]
  ) >>
  PairCases_on `x` >>
  ASM_SIMP_TAC (srw_ss()) [] >>
  rename1 `resolve_array_element _ _ _ _ _ _ = (INL (elem_slot, final_tv, rsubs), rae_st)` >>
  imp_res_tac resolve_array_element_state >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac resolve_array_element_props >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [evaluate_type_def, AllCaseEqs(), LET_THM]) >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME elem_tv'` >>
  Cases_on `final_tv` >>
  ASM_SIMP_TAC (srw_ss()) [bind_apply, return_def, raise_def]
  (* BaseTV, TupleTV, FlagTV, NoneTV: contradiction via leaf_type *)
  >> TRY (Cases_on `rsubs` >> gvs[leaf_type_def] >> NO_TAC)
  (* Remaining: ArrayTV (goal 1), StructTV (goal 2) *)
  >- suspend "ArrayTV_case"
  >> suspend "StructTV_case"
QED

Resume assign_target_pop_value_well_typed[ArrayTV_case]:
  Cases_on `b'` >>
  ASM_SIMP_TAC (srw_ss()) [bind_apply, return_def, raise_def] >>
  strip_tac
  >- suspend "ArrayTV_Fixed"
  >> suspend "ArrayTV_Dynamic"
QED

Resume assign_target_pop_value_well_typed[ArrayTV_Fixed]:
  (* Fixed: read_storage_slot gives well-typed current_val,
     assign_result gives well-typed pop result *)
  (* First establish rsubs = [] *)
  `rsubs = []` by (first_x_assum (qspecl_then [`t'`, `Fixed n`] mp_tac) >> simp[]) >>
  gvs[] >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [bind_apply, return_def, raise_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  (* current_val is well-typed via read_storage_slot_well_typed *)
  `value_has_type (ArrayTV t' (Fixed n)) current_val` by (
    irule (REWRITE_RULE [GSYM AND_IMP_INTRO] read_storage_slot_well_typed) >>
    first_assum (irule_at Any) >>
    gvs[well_formed_type_value_def]
  ) >>
  (* Now apply assign_result_pop_well_typed *)
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] assign_result_pop_well_typed) >>
  disch_then drule >> simp[leaf_type_def] >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM, leaf_type_def]
QED

Resume assign_target_pop_value_well_typed[ArrayTV_Dynamic]:
  (* Dynamic: read_storage_slot gives well-typed popped value *)
  `rsubs = []` by (first_x_assum (qspecl_then [`t'`, `Dynamic n`] mp_tac) >> simp[]) >>
  gvs[leaf_type_def] >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [bind_apply, return_def, raise_def, ignore_bind_apply,
    get_storage_backend_def, check_def, assert_def, AllCaseEqs(), PULL_EXISTS,
    LET_THM] >>
  rpt (COND_CASES_TAC >> simp_tac (srw_ss()) [return_def, raise_def]) >>
  strip_tac >> gvs[] >>
  rpt strip_tac >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] read_storage_slot_well_typed) >>
  first_assum (irule_at Any) >>
  gvs[well_formed_type_value_def]
QED

Resume assign_target_pop_value_well_typed[StructTV_case]:
  (* StructTV: read_storage_slot + assign_result_pop_well_typed *)
  strip_tac >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [bind_apply, return_def, raise_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  (* current_val is well-typed via read_storage_slot_well_typed *)
  `value_has_type (StructTV l) current_val` by (
    irule (REWRITE_RULE [GSYM AND_IMP_INTRO] read_storage_slot_well_typed) >>
    first_assum (irule_at Any) >>
    gvs[well_formed_type_value_def]
  ) >>
  `leaf_type (StructTV l) rsubs = ArrayTV elem_tv' bd` by
    metis_tac[] >>
  `leaf_type (StructTV l) rsubs <> NoneTV` by
    (pop_assum SUBST1_TAC >> REWRITE_TAC[type_value_distinct]) >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] assign_result_pop_well_typed) >>
  rpt (disch_then drule) >> strip_tac >> gvs[]
QED

Resume assign_target_pop_value_well_typed[ScopedVar]:
  (* Unfold assign_target for ScopedVar *)
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [assign_target_def, bind_def, UNCURRY, LET_THM,
                   get_scopes_def, return_def, lift_option_def, raise_def,
                   lift_sum_def, set_scopes_def, ignore_bind_def] >>
  Cases_on `find_containing_scope (string_to_num s) st.scopes` >>
  ASM_SIMP_TAC (srw_ss()) [return_def, raise_def] >>
  PairCases_on `x` >>
  ASM_SIMP_TAC (srw_ss()) [return_def] >>
  ASM_SIMP_TAC (srw_ss()) [type_check_def, assert_def, sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  Cases_on `assign_subscripts x2.type x2.value (REVERSE sbs) PopOp` >>
  ASM_SIMP_TAC (srw_ss()) [return_def, raise_def] >>
  strip_tac >>
  (* Get loc_type FIRST (before gvs destroys st.scopes) *)
  imp_res_tac find_containing_scope_lookup >>
  `loc_type cx st (ScopedVar s) x2.type` by
    (PURE_REWRITE_TAC[loc_type_def] >> qexists_tac `x2` >>
     ASM_REWRITE_TAC[]) >>
  (* Get type connection *)
  drule eval_base_target_type_connection >>
  rpt (disch_then drule) >> strip_tac >>
  (* Get value_has_type from scope_well_typed *)
  imp_res_tac find_containing_scope_structure >>
  `EVERY scope_well_typed st.scopes` by gvs[state_well_typed_def] >>
  `scope_well_typed x1` by (fs[EVERY_APPEND] >> gvs[]) >>
  `value_has_type x2.type x2.value` by
    (fs[scope_well_typed_def] >> res_tac >> gvs[]) >>
  (* leaf_type != NoneTV: substitute tyv, unfold evaluate_type for ArrayT *)
  `leaf_type x2.type (REVERSE sbs) <> NoneTV` by (
    CCONTR_TAC >> gvs[evaluate_type_def, AllCaseEqs(), LET_THM]
  ) >>
  (* Apply assign_result_pop_well_typed *)
  imp_res_tac assign_result_pop_well_typed >>
  (* Connect to evaluate_type ty *)
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM]
QED
Resume assign_target_pop_value_well_typed[ImmutableVar]:
  (* Unfold assign_target for ImmutableVar, step by step *)
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [assign_target_def, LET_THM] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, BETA_THM] >>
  (* Step 1: get_immutables *)
  Cases_on `get_immutables cx (current_module cx) st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def] >>
  (* Step 2: lift_option_type (FLOOKUP imms ni) *)
  Cases_on `FLOOKUP x (string_to_num s)` >>
  simp_tac (srw_ss()) [lift_option_type_def, return_def, raise_def] >>
  rename1 `FLOOKUP imms (string_to_num s) = SOME tva` >>
  (* Step 3: lift_sum (assign_subscripts ...) *)
  Cases_on `assign_subscripts (FST tva) (SND tva) (REVERSE sbs) PopOp` >>
  simp_tac (srw_ss()) [lift_sum_def, return_def, raise_def] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, BETA_THM] >>
  (* Step 4: set_immutable *)
  Cases_on `set_immutable cx (current_module cx) (string_to_num s) (FST tva) x r` >>
  reverse (Cases_on `q`) >>
  ASM_SIMP_TAC (srw_ss()) [raise_def, return_def] >>
  strip_tac >>
  (* Now we have:
     - get_immutables cx src st = (INL imms, r)
     - FLOOKUP imms (string_to_num s) = SOME tva
     - assign_subscripts (FST tva) (SND tva) (REVERSE sbs) PopOp = INL x'
     - assign_result (FST tva) PopOp (SND tva) (REVERSE sbs) r'' = (INL (SOME v), st')
  *)
  (* Get loc_type for ImmutableVar — note: st renamed to r after VAR_EQ_TAC *)
  imp_res_tac get_immutables_state >> rpt BasicProvers.VAR_EQ_TAC >>
  `loc_type cx r (ImmutableVar s) (FST tva)` by (
    PURE_REWRITE_TAC[loc_type_def] >>
    qexistsl_tac [`imms`, `SND tva`] >>
    Cases_on `tva` >> ASM_REWRITE_TAC[]
  ) >>
  (* Get type connection *)
  drule eval_base_target_type_connection >>
  rpt (disch_then drule) >> strip_tac >>
  (* Get value_has_type from immutables well-typedness *)
  Cases_on `tva` >> gvs[] >>
  drule_all immutables_lookup_well_typed >> strip_tac >>
  (* leaf_type != NoneTV — q is FST tva after Cases_on + gvs *)
  `leaf_type q (REVERSE sbs) <> NoneTV` by (
    CCONTR_TAC >> gvs[evaluate_type_def, AllCaseEqs(), LET_THM]
  ) >>
  imp_res_tac assign_result_pop_well_typed >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM]
QED

Finalise assign_target_pop_value_well_typed

Theorem lookup_global_wf:
  !cx src n st tv st'.
    lookup_global cx src n st = (INL tv, st') ==>
    toplevel_value_wf tv
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tv` >> simp[toplevel_value_wf_def] >>
  gvs[lookup_global_def] >>
  pop_assum mp_tac >>
  PURE_ONCE_REWRITE_TAC[bind_def] >>
  simp_tac bool_ss [BETA_THM] >>
  rpt (CASE_TAC >>
       simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def,
                             raise_def, UNCURRY, lift_option_type_def,
                             get_immutables_def]) >>
  rw[] >> gvs[] >>
  imp_res_tac (cj 1 evaluate_type_well_formed)
QED

(* evaluate_subscript: when it returns INL (INL tv), tv is wf *)
Theorem evaluate_subscript_toplevel_wf:
  !tenv tv_ty tv idx res.
    evaluate_subscript tenv tv_ty tv idx = INL (INL res) /\
    toplevel_value_wf tv ==>
    toplevel_value_wf res
Proof
  rpt gen_tac >> Cases_on `tv`
  (* Value: all value constructors produce Value result or error *)
  >- (Cases_on `v` >>
      Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs(), toplevel_value_wf_def] >>
      rw[] >> gvs[toplevel_value_wf_def])
  (* HashMapRef: result is HashMapRef (wf) or INR (not INL INL) *)
  >- (simp[evaluate_subscript_def, AllCaseEqs(), toplevel_value_wf_def] >>
      rw[] >> gvs[])
  (* ArrayRef: elem_tv descends into sub-component *)
  >> (Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs(), LET_THM,
           toplevel_value_wf_def] >>
      strip_tac >> gvs[well_formed_type_value_def])
QED

Theorem evaluate_subscript_storage_wf:
  !tenv tv_ty tv idx is_trans slot rtv.
    evaluate_subscript tenv tv_ty tv idx = INL (INR (is_trans, slot, rtv)) /\
    toplevel_value_wf tv ==>
    well_formed_type_value rtv
Proof
  rpt gen_tac >> Cases_on `tv`
  (* Value: only array_index produces INL, which is INL INL, not INL INR *)
  >- (Cases_on `v` >>
      Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs()])
  (* HashMapRef: INR case uses evaluate_type → well_formed *)
  >- (simp[evaluate_subscript_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac (cj 1 evaluate_type_well_formed))
  (* ArrayRef: elem_tv from wf ArrayRef *)
  >> (Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs(), LET_THM,
           toplevel_value_wf_def] >>
      strip_tac >> gvs[well_formed_type_value_def])
QED

(* IntCall always returns Value _ on success (INL). No induction needed. *)
Theorem intcall_returns_Value[local]:
  !cx ty src_id_opt fn es drv st tv st'.
    eval_expr cx (Call ty (IntCall (src_id_opt,fn)) es drv) st = (INL tv, st') ==>
    ?v. tv = Value v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, UNCURRY, return_def, raise_def,
       ignore_bind_def, LET_THM, COND_RATOR,
       check_def, type_check_def, lift_option_type_def, lift_option_def,
       get_scopes_def, push_function_def,
       finally_def, try_def, handle_function_def, pop_function_def,
       lift_sum_def, lift_sum_runtime_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Uniform tactic for all 20 eval_expr toplevel_wf cases.
   Pre-computes all eval_expr conjuncts (cj 35..54) and tries each.
   Strategy: unfold the right conjunct with gvs-blast (bind_def + AllCaseEqs
   is safe because inner eval_expr/eval_exprs calls are opaque after
   conjunct extraction). Then handle special cases with imp_res_tac. *)
val tv_wf_blast_defs =
  [bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
   UNCURRY, lift_option_type_def, lift_option_def, lift_sum_def,
   lift_sum_runtime_def,
   get_scopes_def, get_immutables_def, get_address_immutables_def,
   get_Value_def, get_accounts_def, get_transient_storage_def,
   lookup_flag_mem_def, check_def, type_check_def, assert_def,
   switch_BoolV_def, LET_THM, COND_RATOR, toplevel_value_wf_def,
   update_accounts_def, update_transient_def, push_log_def];

val ev_expr_cjs = List.tabulate(20, fn i => cj (35+i) evaluate_def);

(* Find pair-typed variables that appear under FST/SND projections
   in assumptions or the goal, and destruct them. *)
fun destruct_pair_vars_tac (asl, g) =
  let
    val all_terms = g :: asl
    fun find_fst_snd_vars t acc =
      if is_comb t then
        let val (f, x) = dest_comb t in
          if is_var x andalso is_const f andalso
             let val nm = fst (dest_const f) in nm = "FST" orelse nm = "SND" end
          then find_fst_snd_vars f (x :: acc)
          else find_fst_snd_vars f (find_fst_snd_vars x acc)
        end
      else if is_abs t then find_fst_snd_vars (body t) acc
      else acc
    val vars_found = List.foldl (fn (t, acc) => find_fst_snd_vars t acc) [] all_terms
    val vars_to_split = op_mk_set aconv vars_found
  in
    if null vars_to_split then ALL_TAC (asl, g)
    else EVERY (List.map (fn v =>
           tmCases_on v ["a__","b__","c__","d__"] >> gvs[]) vars_to_split)
         (asl, g)
  end handle _ => ALL_TAC (asl, g);

(* tv_wf_blast_core: unfold one conjunct, expand bind+case, close with wf.
   Uses rpt strip_tac + VAR_EQ_TAC to combine split assumptions,
   then mp_tac the eval_expr assumption and unfold on the GOAL side only
   (simp_tac, not gvs/fs) to avoid blowing up IH assumptions. *)
(* tv_wf_blast_core: unfold one conjunct, expand bind+case, close with wf.
   Handles: Value-returning cases (trivial), lookup_global (ArrayRef/HashMapRef),
   evaluate_subscript (INL toplevel_value), recursive eval_expr (IH via drule),
   and residual (case ...) st patterns via FULL_CASE_TAC fallback. *)
val tv_wf_case_defs = [return_def, raise_def, toplevel_value_wf_def,
  read_storage_slot_def, bind_def, UNCURRY, lift_option_type_def,
  lift_option_def, get_storage_backend_def];
fun tv_wf_blast_core cj_thm =
  rpt strip_tac >>
  FULL_SIMP_TAC pure_ss [] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[cj_thm] >>
  (* FlagMember: nsid is a pair — Cases_on splits it for lookup_flag_mem_def *)
  TRY (Cases_on `nsid` >> ALL_TAC) >>
  simp_tac (srw_ss()) (tv_wf_blast_defs @ [toplevel_value_wf_def]) >>
  rpt strip_tac >>
  (* Split case expressions in assumptions (handles (case ...) st patterns) *)
  rpt (BasicProvers.FULL_CASE_TAC >> gvs tv_wf_case_defs) >>
  TRY (imp_res_tac lookup_global_wf >>
       gvs[toplevel_value_wf_def] >> NO_TAC) >>
  TRY (imp_res_tac evaluate_subscript_toplevel_wf >>
       gvs[toplevel_value_wf_def] >> NO_TAC) >>
  TRY (imp_res_tac intcall_returns_Value >>
       gvs[toplevel_value_wf_def] >> NO_TAC) >>
  (* IH for recursive eval_expr (IfExp: nested IH with 2 drules) *)
  TRY (first_x_assum (drule_then (drule_then strip_assume_tac)) >>
       gvs[toplevel_value_wf_def] >> NO_TAC) >>
  (* IH for recursive eval_expr (ExtCall: simple drule) *)
  TRY (first_x_assum drule >> strip_tac >>
       gvs[toplevel_value_wf_def] >> NO_TAC) >>
  gvs[toplevel_value_wf_def];

(* Strict version: fails if it doesn't close all subgoals *)
fun tv_wf_blast cj_thm (asl, g) =
  let val (sgs, vf) = tv_wf_blast_core cj_thm (asl, g)
  in if null sgs then (sgs, vf)
     else raise mk_HOL_ERR "tv_wf_blast" "tv_wf_blast" "subgoals remain"
  end;

(* Common tactic for P7 cases that return Value: unfold cj, simplify *)
fun tv_return_value_tac cj_thm extras =
  rpt strip_tac >> gvs (cj_thm :: toplevel_value_wf_def ::
    return_def :: bind_def :: UNCURRY :: AllCaseEqs() :: extras);

(* Standalone lemma: ExtCall result is wf given the decode expression is wf.
   Avoids the IH-matching problem in the induction case. *)
Triviality extcall_returns_wf:
  !cx ty is_static func_name arg_types ret_type es drv st tv st'.
    eval_expr cx (Call ty (ExtCall is_static (func_name,arg_types,ret_type))
                   es drv) st = (INL tv, st') /\
    (!st res st'. eval_expr cx (THE drv) st = (res,st') ==>
       !tv. res = INL tv ==> toplevel_value_wf tv) ==>
    toplevel_value_wf tv
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, UNCURRY, return_def,
       raise_def, LET_THM, COND_RATOR, AllCaseEqs(), PULL_EXISTS,
       lift_option_type_def, lift_option_def, lift_sum_def,
       lift_sum_runtime_def, check_def, type_check_def,
       get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def] >>
  rpt strip_tac >> gvs[toplevel_value_wf_def] >>
  first_x_assum drule >> simp[toplevel_value_wf_def]
QED

(* extcall_toplevel_wf_case removed — handled via suspend/Resume *)

Theorem eval_expr_toplevel_wf:
  (!cx s st res st'. eval_stmt cx s st = (res, st') ==> T) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res, st') ==> T) /\
  (!cx it st res st'. eval_iterator cx it st = (res, st') ==> T) /\
  (!cx g st res st'. eval_target cx g st = (res, st') ==> T) /\
  (!cx gs st res st'. eval_targets cx gs st = (res, st') ==> T) /\
  (!cx bt st res st'. eval_base_target cx bt st = (res, st') ==> T) /\
  (!cx tv nm body vs st res st'. eval_for cx tv nm body vs st = (res, st') ==> T) /\
  (!cx e st res st'. eval_expr cx e st = (res, st') ==>
    !tv. res = INL tv ==> toplevel_value_wf tv) /\
  (!cx es st res st'. eval_exprs cx es st = (res, st') ==> T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >| (
  List.tabulate(34, fn _ => rpt strip_tac >> REWRITE_TAC[TRUTH]) @
  (* 20 P7 eval_expr cases *)
  List.map tv_wf_blast_core
    (List.map (fn i => el i ev_expr_cjs) [1,2,3,4]) @
  [(* 5:IfExp — IH needs two drules: condition eval, then branch eval *)
   tv_wf_blast_core (el 5 ev_expr_cjs) >>
   first_x_assum (drule_then (drule_then strip_assume_tac)) >>
   gvs[toplevel_value_wf_def]] @
  List.map tv_wf_blast_core
    (List.map (fn i => el i ev_expr_cjs) [6,7]) @
  [(* 8:Subscript — IH gives wf for array, then evaluate_subscript_toplevel_wf *)
   tv_wf_blast_core (el 8 ev_expr_cjs) >>
   (* Get toplevel_value_wf tv1 from the direct IH (not the nested one) *)
   qpat_x_assum `!st res st'. eval_expr _ _ st = (res, st') ==> _`
     (drule_then strip_assume_tac) >>
   imp_res_tac evaluate_subscript_toplevel_wf >>
   gvs[toplevel_value_wf_def]] @
  List.map tv_wf_blast_core
    (List.map (fn i => el i ev_expr_cjs) [9,10,11,12,13]) @
  [(* 14:ExtCall *)
   rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> suspend "ExtCall"] @
  List.map tv_wf_blast_core
    (List.map (fn i => el i ev_expr_cjs) [15,16,17,18,19,20]) @
  List.tabulate(2, fn _ => rpt strip_tac >> REWRITE_TAC[TRUTH])
  )
QED

Resume eval_expr_toplevel_wf[ExtCall]:
  (* Normalize guarded IH FIRST, then expand eval_expr Call *)
  qpat_x_assum `!s'' vs t s'3 x t'. _`
    (assume_tac o SIMP_RULE (srw_ss())
      [check_def, type_check_def, lift_option_type_def, lift_option_def,
       lift_sum_def, lift_sum_runtime_def,
       get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def,
       return_def, assert_def, AllCaseEqs(), PULL_EXISTS,
       bind_def, ignore_bind_def, UNCURRY, LET_THM, COND_RATOR]) >>
  (* Expand eval_expr Call *)
  qpat_x_assum `eval_expr _ (Call _ (ExtCall _ _) _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def, UNCURRY,
    return_def, raise_def, LET_THM, AllCaseEqs(), PULL_EXISTS,
    lift_option_type_def, lift_option_def, lift_sum_def,
    lift_sum_runtime_def, check_def, type_check_def,
    get_accounts_def, get_transient_storage_def,
    update_accounts_def, update_transient_def, assert_def, COND_RATOR] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[toplevel_value_wf_def] >>
  (* Decompose all case-of assumptions and result tuple.
     IH-safe: IH was already normalized (no check/lift_option_type). *)
  FULL_SIMP_TAC (srw_ss()) [return_def, raise_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Decompose result tuple: we have FST result, FST (SND result) = [] *)
  PairCases_on `result` >> gvs[] >>
  (* Now case-of run_ext_call resolves and IH should match *)
  FULL_SIMP_TAC (srw_ss()) [return_def, raise_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum irule >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
  simp[]
QED

Finalise eval_expr_toplevel_wf;

(* ===== extract_elements typing ===== *)

(* When we extract elements from a well-typed array, all elements have the
   element type. Needed by For loop (Array iterator case). *)
Theorem extract_elements_well_typed:
  !arr_tv av elem_tv bd vs.
    value_has_type (ArrayTV elem_tv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV elem_tv bd) /\
    extract_elements (ArrayTV elem_tv bd) (ArrayV av) = SOME vs ==>
    EVERY (value_has_type elem_tv) vs
Proof
  rpt gen_tac >>
  simp[extract_elements_def] >>
  Cases_on `av` >> simp[value_has_type_inv]
  (* DynArrayV *)
  >- (rpt strip_tac >> gvs[array_elements_def, all_have_type_EVERY])
  (* SArrayV *)
  >- (rpt strip_tac >> gvs[] >>
      fs[array_elements_def, LET_THM, EVERY_GENLIST] >>
      rpt strip_tac >>
      Cases_on `ALOOKUP l i` >> simp[]
      >- (match_mp_tac default_value_well_typed >> fs[well_formed_type_value_def])
      >> metis_tac[ALOOKUP_sparse_has_type])
QED

(* ===== Range value typing ===== *)
(* For Range iterator: GENLIST of IntV values are well-typed when both
   range bounds have the same int type. The key property is that integer
   type bounds form convex intervals. *)

(* Num elimination: convert Num comparisons to pure integer arithmetic *)
Theorem Num_pos_lt[local]:
  !x (m:num). 0 <= x ==> (Num x < m <=> x < &m)
Proof
  rpt strip_tac >>
  `&(Num x) = x` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum (fn th => REWRITE_TAC[GSYM integerTheory.INT_LT, th])
QED

Theorem Num_pos_le[local]:
  !x (m:num). 0 <= x ==> (Num x <= m <=> x <= &m)
Proof
  rpt strip_tac >>
  `&(Num x) = x` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum (fn th => REWRITE_TAC[GSYM integerTheory.INT_LE, th])
QED

Theorem within_int_bound_convex:
  !b n1 n2 k.
    within_int_bound b n1 /\ within_int_bound b n2 /\
    n1 <= n2 /\ &k < n2 - n1 ==>
    within_int_bound b (n1 + &k)
Proof
  Cases_on `b` >> simp[within_int_bound_def] >> rpt strip_tac
  (* Signed *)
  >- (
    Cases_on `n = 0` >- gvs[] >>
    gvs[] >>
    Cases_on `n1 + &k < 0` >> simp[]
    (* n1+&k < 0: need Num(-(n1+&k)) <= 2^(n-1) *)
    >- (
      `n1 < 0` by intLib.ARITH_TAC >> fs[] >>
      `0 <= -(n1 + &k)` by intLib.ARITH_TAC >>
      `0 <= -n1` by intLib.ARITH_TAC >>
      `-(n1 + &k) <= -n1` by intLib.ARITH_TAC >>
      fs[Num_pos_le] >> intLib.ARITH_TAC)
    (* n1+&k >= 0: need Num(n1+&k) < 2^(n-1) *)
    >- (
      Cases_on `n2 < 0`
      >- (`n1 + &k < n2` by intLib.ARITH_TAC >> intLib.ARITH_TAC)
      >- (
        fs[] >>
        `0 <= n1 + &k` by intLib.ARITH_TAC >>
        `0 <= n2` by intLib.ARITH_TAC >>
        `n1 + &k < n2` by intLib.ARITH_TAC >>
        `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
        simp[])))
  (* Unsigned: Num(n1+&k) < 2^n *)
  >- (
    `0 <= n1 + &k` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &k < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[])
QED

Theorem range_values_well_typed:
  !n1 n2 count tyv.
    value_has_type tyv (IntV n1) /\
    value_has_type tyv (IntV n2) /\
    get_range_limits (IntV n1) (IntV n2) = INL (n1, count) ==>
    EVERY (value_has_type tyv) (GENLIST (\n. IntV (n1 + &n)) count)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[get_range_limits_def] >>
  simp[EVERY_GENLIST] >> rpt strip_tac >>
  (* Convert n < Num(n2 - n1) to &n < n2 - n1 *)
  `0 <= n2 - n1` by intLib.ARITH_TAC >>
  `&n < n2 - n1` by (
    `&(Num (n2 - n1)) = n2 - n1` by metis_tac[integerTheory.INT_OF_NUM] >>
    intLib.ARITH_TAC) >>
  Cases_on `tyv` >> gvs[value_has_type_def] >>
  Cases_on `b` >> gvs[value_has_type_def]
  (* UintT (Unsigned): Num(n1+&n) < 2^n' *)
  >- (
    `0 <= n1 + &n` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &n < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &n) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[])
  (* IntT (Signed): within_int_bound form *)
  >- metis_tac[within_int_bound_convex]
QED


(* ===== Scope bracket decomposition ===== *)
(* Decomposes `do push_scope; finally (eval_stmts cx ss) pop_scope od`
   into eval_stmts on a pushed state + pop. Eliminates the need to manually
   reason about finally/pop_scope in If/For cases. *)
Theorem scope_bracket_decompose:
  !cx ss st res st'.
    (do push_scope; finally (eval_stmts cx ss) pop_scope od) st = (res, st') ==>
    ?q st_body.
      eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      (((?x. q = INL x) ==> res = INL ()) /\
       (!e. q = INR e ==> res = INR e))
Proof
  rpt strip_tac >>
  gvs[push_scope_def, finally_def, pop_scope_def,
      return_def, raise_def, bind_def, ignore_bind_def,
      AllCaseEqs(), BETA_THM] >>
  Cases_on `(eval_stmts cx ss (st with scopes updated_by CONS FEMPTY))` >>
  Cases_on `q` >>
  gvs[AllCaseEqs(), pop_scope_def, return_def, raise_def] >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `r.scopes` >> gvs[return_def, raise_def,
    evaluation_state_component_equality]
QED

(* Combined: scope bracket preserves state_well_typed + env_consistent.
   Use after scope_bracket_decompose gives you the body state. *)
Theorem scope_bracket_preserves:
  !cx ss st q st_body env.
    eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
    state_well_typed st_body /\
    env_consistent env cx st_body ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac
  >- (drule scope_bracket_preserves_swt >> simp[])
  >> mp_tac (Q.SPECL [`env`, `cx`, `st`, `FEMPTY`, `ss`, `q`, `st_body`]
               scope_bracket_preserves_ec) >>
  simp[]
QED


(* Decomposition of for-loop body:
   finally (try do eval_stmts cx body; return F od handle_loop_exception)
     pop_scope st_push
   reduces to eval_stmts cx body st_push with scope popping *)
Theorem for_body_decompose:
  !cx body st sc res st'.
    finally (try do eval_stmts cx body; return F od handle_loop_exception)
      pop_scope (st with scopes updated_by CONS sc) = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body (st with scopes updated_by CONS sc) =
        (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply, BETA_THM,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body (st with scopes updated_by CONS sc)` >>
  `?hd tl. r.scopes = hd :: tl` by (
    imp_res_tac eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED


(* Monadic chain decomposition for Append:
   eval_base_target >> eval_expr >> materialise >> assign_target >> return () *)
Theorem append_chain_decompose:
  eval_stmt cx (Append bt e) st = (res, st') ==>
  (* Success: all steps return INL *)
  (?loc sbs st1 tv st2 v.
     eval_base_target cx bt st = (INL (loc,sbs), st1) /\
     eval_expr cx e st1 = (INL tv, st2) /\
     materialise cx tv st2 = (INL v, st2) /\
     (?at_res. assign_target cx (BaseTargetV loc sbs) (AppendOp v) st2 =
       (INL at_res, st')) /\
     res = INL ()) \/
  (* Error at step 1: eval_base_target *)
  (?err st1. eval_base_target cx bt st = (INR err, st1) /\
     res = INR err /\ st' = st1) \/
  (* Error at step 2: eval_expr *)
  (?loc sbs st1 err st2.
     eval_base_target cx bt st = (INL (loc,sbs), st1) /\
     eval_expr cx e st1 = (INR err, st2) /\ res = INR err /\ st' = st2) \/
  (* Error at step 3: materialise *)
  (?loc sbs st1 tv st2 err.
     eval_base_target cx bt st = (INL (loc,sbs), st1) /\
     eval_expr cx e st1 = (INL tv, st2) /\
     materialise cx tv st2 = (INR err, st2) /\ res = INR err /\ st' = st2) \/
  (* Error at step 4: assign_target *)
  (?loc sbs st1 tv st2 v err.
     eval_base_target cx bt st = (INL (loc,sbs), st1) /\
     eval_expr cx e st1 = (INL tv, st2) /\
     materialise cx tv st2 = (INL v, st2) /\
     assign_target cx (BaseTargetV loc sbs) (AppendOp v) st2 =
       (INR err, st') /\
     res = INR err)
Proof
  simp[Once evaluate_def, bind_def, UNCURRY, return_def,
       raise_def, ignore_bind_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  TRY (imp_res_tac materialise_state >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  TRY (Cases_on `x''` >> gvs[] >> metis_tac[]) >>
  TRY (Cases_on `x'` >> gvs[] >> metis_tac[]) >>
  TRY (Cases_on `x` >> gvs[] >> metis_tac[])
QED


(* ================================================================= *)
(* eval_iterator preserves env_consistent                             *)
(* Proved by unfolding evaluate_def for Array/Range, using            *)
(* eval_expr_preserves_ec + pure op state preservation lemmas.        *)
(* ================================================================= *)

val bind_apply_local = SIMP_RULE std_ss [FUN_EQ_THM] bind_def;

(*
 * Helper: any monadic chain of state-preserving ops after eval_expr
 * preserves env_consistent. Works by showing st' = st_after_eval_expr
 * for all pure ops, then using eval_expr_preserves_ec.
 *)
Theorem eval_iterator_preserves_ec:
  !cx it st res st' env.
    env_consistent env cx st /\
    eval_iterator cx it st = (res, st') ==>
    env_consistent env cx st'
Proof
  Cases_on `it` >>
  simp[Once evaluate_def, bind_def, UNCURRY, return_def, raise_def] >>
  rpt gen_tac >> strip_tac
  (* Array case *)
  >- (
    (* eval_expr is the only stateful op, rest are pure *)
    Cases_on `eval_expr cx e st` >> rename1 `(res1, st1)` >>
    gvs[] >>
    `env_consistent env cx st1` by (
      irule eval_expr_preserves_ec >> metis_tac[]) >>
    (* materialise doesn't change state *)
    Cases_on `res1` >> gvs[] >>
    Cases_on `materialise cx x st1` >> rename1 `(res2, st2)` >>
    `st2 = st1` by (imp_res_tac materialise_state >> gvs[]) >>
    gvs[] >>
    (* lift_option_type / extract_elements are pure *)
    gvs[lift_option_type_def, return_def, raise_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
  )
  (* Range case: two eval_expr calls, everything else pure *)
  >- (
    qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac >>
    simp[get_Value_def, lift_sum_def, return_def, raise_def] >>
    rpt (CASE_TAC >> simp[]) >>
    rpt strip_tac >> gvs[] >>
    imp_res_tac eval_expr_preserves_ec >>
    imp_res_tac get_Value_state >> gvs[return_def, raise_def] >>
    first_x_assum drule >> simp[]
  )
QED


(* ===== evaluate_binop preserves value_has_type ===== *)

val eb_defs = [evaluate_binop_def, bounded_int_op_def, bounded_decimal_op_def,
               AllCaseEqs(), within_int_bound_def];

(* --- Helper: int mod bounds in raw Num form --- *)
Theorem int_mod_pow2_bounds[local]:
  !i m. 0 <= i % &(2 ** m) /\ Num (i % &(2 ** m)) < 2 ** m
Proof
  rpt gen_tac >>
  `0i < &(2 ** m)` by simp[] >>
  `&(2 ** m) <> 0i` by intLib.ARITH_TAC >>
  drule integerTheory.INT_MOD_BOUNDS >>
  disch_then (qspec_then `i` strip_assume_tac) >> gvs[] >>
  `&(Num (i % &(2 ** m))) = i % &(2 ** m)` by
    (simp[Once (GSYM integerTheory.INT_OF_NUM)]) >>
  intLib.ARITH_TAC
QED

(* Bridge lemmas: convert Num comparisons to pure int *)
Theorem NUM_LT_INT[local]:
  !x (n:num). 0 <= x ==> (Num x < n <=> x < &n)
Proof
  rpt strip_tac >>
  `x = &(Num x)` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum SUBST_ALL_TAC >> simp[integerTheory.INT_OF_NUM_LT]
QED

Theorem NUM_LE_INT[local]:
  !x (n:num). 0 <= x ==> (Num x <= n <=> x <= &n)
Proof
  rpt strip_tac >>
  `x = &(Num x)` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum SUBST_ALL_TAC >> simp[integerTheory.INT_OF_NUM_LE]
QED

(* Pure-int characterization of within_int_bound (Signed m) *)
Theorem within_int_bound_signed_int[local]:
  !m i. 0 < m ==>
        (within_int_bound (Signed m) i <=>
         -&(2 ** (m - 1)) <= i /\ i < &(2 ** (m - 1)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[within_int_bound_def, LET_THM] >>
  Cases_on `i < 0`
  >- (
    simp[] >>
    `0 <= -i` by intLib.ARITH_TAC >>
    simp[NUM_LE_INT] >>
    `0 <= &(2 ** (m - 1))` by simp[] >>
    EQ_TAC >> strip_tac >> intLib.ARITH_TAC
  )
  >- (
    simp[] >>
    `0 <= i` by intLib.ARITH_TAC >>
    simp[NUM_LT_INT] >>
    `0 <= &(2 ** (m - 1))` by simp[] >>
    EQ_TAC >> strip_tac >> intLib.ARITH_TAC
  )
QED

(* --- Helper: signed_int_mod preserves within_int_bound (Signed m) --- *)
Theorem signed_int_mod_within_bound[local]:
  !m i. 0 < m ==> within_int_bound (Signed m) (signed_int_mod m i)
Proof
  rpt strip_tac >>
  simp[within_int_bound_signed_int, signed_int_mod_def, LET_THM] >>
  `2 ** m = 2 * 2 ** (m - 1)` by
    (`m = SUC (m - 1)` by simp[] >> pop_assum SUBST1_TAC >> simp[EXP]) >>
  `&(2 ** m) <> 0i` by simp[] >>
  `0i < &(2 ** m)` by simp[] >>
  drule integerTheory.INT_MOD_BOUNDS >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  qabbrev_tac `r = i % &(2 ** m)` >>
  Cases_on `r >= &(2 ** (m - 1))` >> simp[] >>
  (* Both cases: abstract &(2^(m-1)) to pure int var, use ARITH_TAC *)
  qpat_x_assum `Abbrev _` kall_tac >>
  `~(&(2 ** m) < 0i)` by simp[] >> fs[] >>
  pop_assum kall_tac >>
  qpat_x_assum `2 ** m = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE[th, GSYM integerTheory.INT_MUL]) >>
    PURE_REWRITE_TAC[th, GSYM integerTheory.INT_MUL]) >>
  qabbrev_tac `k = &(2 ** (m - 1)):int` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  intLib.ARITH_TAC
QED

(* --- int_shift_right bounds machinery --- *)

(* num_of_bits is the left-inverse of bits_of_num.
   Derived from int_of_bits_bits_of_int + int_of_bits_def + bits_of_int_def *)
Theorem num_of_bits_bits_of_num[local]:
  !n. num_of_bits (bits_of_num n) = n
Proof
  gen_tac >>
  mp_tac (Q.SPEC `&n` int_bitwiseTheory.int_of_bits_bits_of_int) >>
  simp[int_bitwiseTheory.bits_of_int_def, int_bitwiseTheory.int_of_bits_def]
QED

(* Dropping bits from the front reduces num_of_bits *)
Theorem num_of_bits_drop_le[local]:
  !bs m. num_of_bits (DROP m bs) <= num_of_bits bs
Proof
  Induct >>
  simp[int_bitwiseTheory.num_of_bits_def, listTheory.DROP_def] >>
  rpt gen_tac >> Cases_on `m` >>
  simp[int_bitwiseTheory.num_of_bits_def] >>
  Cases_on `h` >> simp[int_bitwiseTheory.num_of_bits_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* MAP commutes with DROP *)
Theorem MAP_DROP[local]:
  !f bs m. MAP f (DROP m bs) = DROP m (MAP f bs)
Proof
  gen_tac >> Induct >> simp[listTheory.DROP_def] >>
  rpt gen_tac >> Cases_on `m` >> simp[listTheory.DROP_def]
QED

(* int_shift_right of non-negative is non-negative and bounded *)
Theorem int_shift_right_nonneg_bounds[local]:
  !m i. 0 <= i ==> 0 <= int_shift_right m i /\ int_shift_right m i <= i
Proof
  rpt strip_tac >> (
    `~(i < 0)` by intLib.ARITH_TAC >>
    simp[int_bitwiseTheory.int_shift_right_def,
         int_bitwiseTheory.bits_of_int_def,
         int_bitwiseTheory.int_of_bits_def, LET_THM,
         pairTheory.UNCURRY_DEF] >>
    `num_of_bits (DROP m (bits_of_num (Num i))) <=
     num_of_bits (bits_of_num (Num i))` by simp[num_of_bits_drop_le] >>
    fs[num_of_bits_bits_of_num] >>
    metis_tac[integerTheory.INT_OF_NUM, integerTheory.INT_LE,
              integerTheory.INT_LE_TRANS]
  )
QED

(* int_shift_right of negative is negative and >= the original *)
Theorem int_shift_right_neg_bounds[local]:
  !m i. i < 0 ==> int_shift_right m i < 0 /\ i <= int_shift_right m i
Proof
  rpt strip_tac >> (
    qabbrev_tac `k = Num (-i - 1)` >>
    `0 <= -i - 1` by intLib.ARITH_TAC >>
    `int_not i = -i - 1` by simp[int_bitwiseTheory.int_not_def] >>
    simp[int_bitwiseTheory.int_shift_right_def,
         int_bitwiseTheory.bits_of_int_def, LET_THM,
         pairTheory.UNCURRY_DEF] >>
    simp[int_bitwiseTheory.int_of_bits_def, MAP_DROP] >>
    simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
    `num_of_bits (DROP m (bits_of_num k)) <= k` by
      metis_tac[num_of_bits_drop_le, num_of_bits_bits_of_num,
                LESS_EQ_TRANS] >>
    simp[int_bitwiseTheory.int_not_def] >>
    `&k = -i - 1` by
      (qunabbrev_tac `k` >>
       metis_tac[integerTheory.INT_OF_NUM]) >>
    qabbrev_tac `j = num_of_bits (DROP m (bits_of_num k))` >>
    `&j <= &k` by simp[integerTheory.INT_LE] >>
    intLib.ARITH_TAC
  )
QED

(* Combined: int_shift_right preserves within_int_bound *)
Theorem int_shift_right_within_bound[local]:
  !m n i. 0 < n /\ within_int_bound (Signed n) i ==>
          within_int_bound (Signed n) (int_shift_right m i)
Proof
  rpt strip_tac >>
  `!j. within_int_bound (Signed n) j <=> -&(2 ** (n-1)) <= j /\ j < &(2 ** (n-1))`
    by simp[within_int_bound_signed_int] >>
  fs[] >>
  Cases_on `0 <= i`
  >- (
    drule int_shift_right_nonneg_bounds >>
    disch_then (qspec_then `m` strip_assume_tac) >>
    intLib.ARITH_TAC
  )
  >- (
    `i < 0` by intLib.ARITH_TAC >>
    drule int_shift_right_neg_bounds >>
    disch_then (qspec_then `m` strip_assume_tac) >>
    intLib.ARITH_TAC
  )
QED

(* Unsigned variant *)
Theorem int_shift_right_unsigned_bounds[local]:
  !m n i. 0 <= i /\ i < &(2 ** n) ==>
          0 <= int_shift_right m i /\ int_shift_right m i < &(2 ** n)
Proof
  rpt strip_tac >>
  drule int_shift_right_nonneg_bounds >>
  disch_then (qspec_then `m` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

(* evaluate_binop preserves value_has_type when both operands are well-typed
   and u matches tv's integer bound. *)
(* Helper for IntV case of evaluate_binop_preserves_vht *)
Theorem evaluate_binop_intv_preserves_vht[local]:
  !u tv2 bop i v result bt.
    evaluate_binop u tv2 bop (IntV i) v = INL result /\
    value_has_type (BaseTV bt) (IntV i) /\ value_has_type (BaseTV bt) v /\
    well_formed_type_value (BaseTV bt) /\
    (!m. bt = UintT m ==> u = Unsigned m) /\
    (!m. bt = IntT m ==> u = Signed m) /\
    bop <> Eq /\ bop <> NotEq /\ bop <> Lt /\ bop <> LtE /\
    bop <> Gt /\ bop <> GtE /\ bop <> In /\ bop <> NotIn ==>
    value_has_type (BaseTV bt) result
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt` >> gvs[value_has_type_def, well_formed_type_value_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `bop` >>
  gvs[evaluate_binop_def, bounded_int_op_def, wrapped_int_op_def,
      bounded_decimal_op_def, binop_negate_def,
      AllCaseEqs(), LET_THM, value_has_type_def,
      int_bound_bits_def] >>
  TRY (gvs[within_int_bound_def] >> NO_TAC) >>
  (* Unsigned Exp: w2n < dimword(:256) *)
  TRY (
    PURE_REWRITE_TAC[GSYM (EVAL ``dimword (:256)``)] >>
    MATCH_ACCEPT_TAC wordsTheory.w2n_lt >> NO_TAC) >>
  (* Unsigned ShR: bridge nat<->int, use int_shift_right_unsigned_bounds *)
  TRY (
    qspecl_then [`Num i'`, `n`, `i`] mp_tac int_shift_right_unsigned_bounds >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >> irule (iffLR NUM_LT_INT) >> ASM_REWRITE_TAC[])) >>
    strip_tac >>
    conj_tac >- ASM_REWRITE_TAC[] >>
    irule (iffRL NUM_LT_INT) >> ASM_REWRITE_TAC[] >> NO_TAC) >>
  (* Now unfold within_int_bound_def for remaining goals *)
  TRY (Cases_on `n = 0` >> gvs[within_int_bound_def] >>
       gvs[bounded_int_op_def, wrapped_int_op_def, within_int_bound_def,
           AllCaseEqs()] >> NO_TAC) >>
  gvs[within_int_bound_def] >>
  (* Unsigned mod: x % &(2^n) is in [0, 2^n) *)
  TRY (simp_tac (srw_ss()) [int_mod_pow2_bounds] >> NO_TAC) >>
  (* Min/Max: nested IF_CASES_TAC *)
  rw[] >> gvs[] >>
  TRY (drule signed_int_mod_within_bound >>
       rw[within_int_bound_def] >>
       qmatch_goalsub_abbrev_tac`signed_int_mod _ ii` >>
       first_x_assum(qspec_then`ii`mp_tac) >> rw[]) >>
  TRY (
    drule int_shift_right_within_bound >>
    rw[within_int_bound_def] >>
    qmatch_goalsub_abbrev_tac`int_shift_right mm ii` >>
    first_x_assum(qspecl_then[`mm`,`ii`]mp_tac) >>
    rw[]) >>
  EVAL_TAC
QED

(* int_bitwise on non-negative bounded naturals agrees with BITWISE *)
Theorem int_bitwise_eq_BITWISE[local]:
  !f a b k. a < 2**k /\ b < 2**k /\ ~f F F ==>
    int_bitwise f (&a) (&b) = &(BITWISE k f a b)
Proof
  rpt strip_tac >>
  simp[int_bitwiseTheory.int_bit_equiv] >>
  gen_tac >>
  simp[int_bitwiseTheory.int_bit_bitwise, int_bitwiseTheory.int_bit_def] >>
  Cases_on `n < k` >- (
    (* n < k: BITWISE_THM gives BIT n (BITWISE k f a b) = f (BIT n a) (BIT n b) *)
    `~((&(BITWISE k f a b)):int < 0)` by simp[] >>
    ASM_SIMP_TAC std_ss [integerTheory.NUM_OF_INT] >>
    simp[bitTheory.BITWISE_THM]
  ) >>
  (* n >= k: both sides are F *)
  `~((&a):int < 0) /\ ~((&b):int < 0)` by simp[] >>
  ASM_SIMP_TAC std_ss [integerTheory.NUM_OF_INT] >>
  `~BIT n a` by (irule bitTheory.NOT_BIT_GT_TWOEXP >>
                  irule LESS_LESS_EQ_TRANS >> qexists_tac `2**k` >>
                  simp[]) >>
  `~BIT n b` by (irule bitTheory.NOT_BIT_GT_TWOEXP >>
                  irule LESS_LESS_EQ_TRANS >> qexists_tac `2**k` >>
                  simp[]) >>
  ASM_REWRITE_TAC[] >>
  `~((&(BITWISE k f a b)):int < 0)` by simp[] >>
  ASM_SIMP_TAC std_ss [integerTheory.NUM_OF_INT] >>
  irule bitTheory.NOT_BIT_GT_TWOEXP >>
  irule LESS_LESS_EQ_TRANS >> qexists_tac `2**k` >>
  simp[bitTheory.BITWISE_LT_2EXP]
QED

(* Corollary: int_bitwise on bounded nats is bounded *)
Theorem int_bitwise_nat_bound[local]:
  !f a b k. a < 2**k /\ b < 2**k /\ ~f F F ==>
    0 <= int_bitwise f (&a) (&b) /\ Num (int_bitwise f (&a) (&b)) < 2**k
Proof
  rpt strip_tac >>
  qspecl_then [`f`,`a`,`b`,`k`] mp_tac int_bitwise_eq_BITWISE >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  ASM_REWRITE_TAC[] >> simp[bitTheory.BITWISE_LT_2EXP]
QED

(* Int division upper bound: x / d < n implies x < n * d *)
Theorem int_div_lt_imp[local]:
  !x d (n:int). 0 <= x /\ 0 < d /\ x / d < n ==> x < n * d
Proof
  rpt strip_tac >>
  `?xn. x = &xn` by (qexists_tac `Num x` >> fs[integerTheory.INT_OF_NUM]) >>
  `?dn. d = &dn /\ 0 < dn`
    by (qexists_tac `Num d` >> fs[integerTheory.INT_OF_NUM,
          integerTheory.INT_LT] >> intLib.ARITH_TAC) >>
  `&dn <> (0:int)` by intLib.ARITH_TAC >>
  fs[integerTheory.INT_DIV] >>
  `0 <= (n:int)` by (spose_not_then assume_tac >>
    fs[integerTheory.INT_NOT_LE] >> intLib.ARITH_TAC) >>
  `?nn. n = &nn` by (qexists_tac `Num n` >> fs[integerTheory.INT_OF_NUM]) >>
  fs[integerTheory.INT_LT, integerTheory.INT_MUL] >>
  fs[arithmeticTheory.DIV_LT_X]
QED

(* Helper for DecimalV Mul: word-level division by 10^10 preserves Signed 168
   bound when ABS(p)/10^10 is already bounded.
   Chain: ABS(p)/10^10 bounded -> |p| < 2^255 -> word ops faithful ->
          w2i(i2w(p)/10^10w) = p quot 10^10, and ABS(p quot d) = ABS(p)/d *)
Theorem decimal_mul_word_bound[local]:
  !p. within_int_bound (Signed 168) (ABS p / 10000000000) ==>
      within_int_bound (Signed 168)
        (w2i ((i2w p : bytes32) / 10000000000w))
Proof
  rpt strip_tac >>
  (* Step 1: ABS p / 10^10 < 2^167, hence ABS p < 2^167 * 10^10 < 2^255 *)
  `ABS p / 10000000000 < 2 ** 167`
    by (qpat_x_assum `within_int_bound _ _` mp_tac >>
        simp[within_int_bound_def, LET_THM] >>
        `0 <= ABS p / 10000000000` by
          (simp[integerTheory.int_div, integerTheory.INT_ABS] >>
           Cases_on `0 <= p` >> simp[] >> intLib.ARITH_TAC) >>
        intLib.ARITH_TAC) >>
  `ABS p < 2 ** 167 * 10000000000`
    by (qspecl_then [`ABS p`, `10000000000`, `2 ** 167`] mp_tac int_div_lt_imp >>
        simp[integerTheory.INT_ABS_POS]) >>
  `ABS p < 2 ** 255`
    by (`(2:int) ** 167 * 10000000000 < 2 ** 255` by EVAL_TAC >>
        intLib.ARITH_TAC) >>
  (* Step 2: within_int_bound (Signed 256) p, so w2i(i2w p) = p *)
  `within_int_bound (Signed 256) p`
    by (simp[within_int_bound_def, LET_THM] >>
        Cases_on `p < 0` >>
        fs[integerTheory.INT_ABS, integerTheory.INT_NOT_LT] >>
        intLib.ARITH_TAC) >>
  `w2i (i2w p : bytes32) = p`
    by (qspecl_then [`p`, `256`] mp_tac w2i_i2w_within_signed >> simp[]) >>
  (* Step 3: word_quot gives i2w(p quot 10^10) *)
  `(10000000000w : bytes32) <> 0w` by EVAL_TAC >>
  `w2i (10000000000w : bytes32) = 10000000000`
    by EVAL_TAC >>
  `(i2w p : bytes32) / 10000000000w = i2w (p quot 10000000000)`
    by (drule integer_wordTheory.word_quot >>
        disch_then (qspec_then `i2w p` mp_tac) >> simp[]) >>
  (* Step 4: ABS(p quot 10^10) = ABS(p) / 10^10 *)
  `ABS (p quot 10000000000) = ABS p / 10000000000`
    by (`(10000000000:int) <> 0` by intLib.ARITH_TAC >>
        simp[integerTheory.int_quot, integerTheory.int_div] >>
        Cases_on `0 <= p` >> simp[integerTheory.INT_ABS] >>
        intLib.ARITH_TAC) >>
  (* Step 5: within_int_bound (Signed 168) (p quot 10^10) from hypothesis *)
  `within_int_bound (Signed 168) (p quot 10000000000)`
    by (qpat_x_assum `within_int_bound _ (ABS p / _)` mp_tac >>
        simp[within_int_bound_def, LET_THM] >>
        Cases_on `p quot 10000000000 < 0` >>
        Cases_on `ABS p / 10000000000 < 0` >> fs[] >>
        intLib.ARITH_TAC) >>
  (* Step 6: w2i(i2w(result)) = result, widen 168 -> 256 *)
  `within_int_bound (Signed 256) (p quot 10000000000)`
    by (qpat_x_assum `within_int_bound (Signed 168) _` mp_tac >>
        simp[within_int_bound_def, LET_THM] >>
        Cases_on `p quot 10000000000 < 0` >> fs[] >> intLib.ARITH_TAC) >>
  `w2i (i2w (p quot 10000000000) : bytes32) = p quot 10000000000`
    by (qspecl_then [`p quot 10000000000`, `256`] mp_tac w2i_i2w_within_signed >>
        simp[]) >>
  simp[]
QED

Theorem evaluate_binop_preserves_vht:
  !u tv2 bop a v result tv.
    evaluate_binop u tv2 bop a v = INL result /\
    value_has_type tv a /\ value_has_type tv v /\
    well_formed_type_value tv /\
    (!m. tv = BaseTV (UintT m) ==> u = Unsigned m) /\
    (!m. tv = BaseTV (IntT m) ==> u = Signed m) /\
    bop <> Eq /\ bop <> NotEq /\ bop <> Lt /\ bop <> LtE /\
    bop <> Gt /\ bop <> GtE /\ bop <> In /\ bop <> NotIn ==>
    value_has_type tv result
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `a` >>
  fs[value_has_type_def, well_formed_type_value_def] >>
  Cases_on `tv` >> fs[value_has_type_def] >>
  gvs[value_has_type_def, well_formed_type_value_def] >>
  (* IntV: forward-resolve intv helper via evaluate_binop assumption *)
  TRY (
    drule evaluate_binop_intv_preserves_vht >>
    disch_then (qspec_then `b` mp_tac) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    strip_tac >> NO_TAC) >>
  (* Remaining: non-IntV cases. Most evaluate_binop calls return error. *)
  Cases_on `bop` >>
  gvs[evaluate_binop_def, AllCaseEqs(), value_has_type_def,
      binop_negate_def, bounded_decimal_op_def, within_int_bound_def] >>
  (* BoolV: result is BoolV, b' must be BoolT *)
  TRY (Cases_on `b'` >> gvs[value_has_type_def, well_formed_type_value_def] >>
       NO_TAC) >>
  (* DecimalV: within_int_bound check already in assumptions *)
  TRY (Cases_on `b` >> gvs[value_has_type_def, well_formed_type_value_def,
       within_int_bound_def] >> NO_TAC) >>
  (* FlagV: bitwise ops on bounded nats — unfold to int_bitwise, apply bound *)
  PURE_REWRITE_TAC[int_bitwiseTheory.int_and_def, int_bitwiseTheory.int_or_def,
                   int_bitwiseTheory.int_xor_def] >>
  TRY (
    qspecl_then [`$/\`,`n`,`n2`,`n'`] mp_tac int_bitwise_nat_bound >>
    ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[] >> NO_TAC) >>
  TRY (
    qspecl_then [`$\/`,`n`,`n2`,`n'`] mp_tac int_bitwise_nat_bound >>
    ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[] >> NO_TAC) >>
  TRY (
    qspecl_then [`\x y:bool. x <> y`,`n`,`n2`,`n'`] mp_tac int_bitwise_nat_bound >>
    simp_tac std_ss [] >>
    ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[] >> NO_TAC) >>
  (* DecimalV: remaining cases (Mul, Min, Max) *)
  Cases_on `b` >> gvs[value_has_type_def, well_formed_type_value_def,
       within_int_bound_def] >>
  (* Min/Max: case split on i < i2, use corresponding bound *)
  TRY (rpt IF_CASES_TAC >> gvs[] >> NO_TAC) >>
  (* Mul: word-level decimal multiplication — apply decimal_mul_word_bound *)
  `within_int_bound (Signed 168) (ABS (i * i2) / 10000000000)`
    by (simp[within_int_bound_def, LET_THM]) >>
  drule decimal_mul_word_bound >>
  simp[within_int_bound_def, LET_THM]
QED

(* Shift variant: v (the shift amount) may have a different type.
   ShL uses int_mod/signed_int_mod (wrapped), ShR uses int_shift_right.
   Only IntV values have shifts. *)
Theorem evaluate_binop_shift_preserves_vht:
  !u tv2 bop a v result tv.
    (bop = ShL \/ bop = ShR) /\
    evaluate_binop u tv2 bop a v = INL result /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    (!m. tv = BaseTV (UintT m) ==> u = Unsigned m) /\
    (!m. tv = BaseTV (IntT m) ==> u = Signed m) ==>
    value_has_type tv result
Proof
  rpt gen_tac >> strip_tac >>
  (* Only IntV + BaseTV (UintT/IntT) has shift ops defined *)
  Cases_on `a` >> Cases_on `tv` >>
  gvs[value_has_type_def, well_formed_type_value_def] >>
  (* Eliminate non-IntV and non-BaseTV cases: ShL/ShR returns error *)
  TRY (Cases_on `v` >>
       gvs[evaluate_binop_def, AllCaseEqs()] >> NO_TAC) >>
  (* Remaining: a = IntV i, tv = BaseTV b *)
  Cases_on `b` >> gvs[value_has_type_def, well_formed_type_value_def] >>
  Cases_on `v` >>
  gvs[evaluate_binop_def, AllCaseEqs(), LET_THM, value_has_type_def,
      int_bound_bits_def] >>
  TRY (gvs[within_int_bound_def] >> NO_TAC) >>
  (* ShR: keep within_int_bound folded *)
  TRY (  (* Unsigned ShR *)
    qspecl_then [`Num i'`, `n`, `i`] mp_tac int_shift_right_unsigned_bounds >>
    (impl_tac >- (
      ASM_REWRITE_TAC[] >> irule (iffLR NUM_LT_INT) >> ASM_REWRITE_TAC[])) >>
    strip_tac >>
    conj_tac >- ASM_REWRITE_TAC[] >>
    irule (iffRL NUM_LT_INT) >> ASM_REWRITE_TAC[] >> NO_TAC) >>
  (* Remaining signed goals: ShR and ShL *)
  gvs[within_int_bound_def] >>
  TRY (simp_tac (srw_ss()) [int_mod_pow2_bounds] >> NO_TAC) >>
  rw[] >> gvs[] >>
  TRY (drule signed_int_mod_within_bound >>
       rw[within_int_bound_def] >>
       qmatch_goalsub_abbrev_tac`signed_int_mod _ ii` >>
       first_x_assum(qspec_then`ii`mp_tac) >> rw[]) >>
  TRY (
    drule int_shift_right_within_bound >>
    rw[within_int_bound_def] >>
    qmatch_goalsub_abbrev_tac`int_shift_right mm ii` >>
    first_x_assum(qspecl_then[`mm`,`ii`]mp_tac) >>
    rw[]) >>
  `!m. int_shift_right m 0 = 0` by
    simp[int_bitwiseTheory.int_shift_right_def,
         EVAL ``bits_of_int 0``, EVAL ``int_of_bits ([],F)``] >>
  `!m. int_shift_left m 0 = 0` by (
    simp[int_bitwiseTheory.int_shift_left_def,
         EVAL ``bits_of_int 0``,
         int_bitwiseTheory.int_of_bits_def,
         int_bitwiseTheory.num_of_bits_def] >>
    Induct_on `m` >>
    simp[int_bitwiseTheory.num_of_bits_def,
         rich_listTheory.GENLIST_K_CONS]) >>
  `!x. signed_int_mod 0 x = 0` by
    simp[signed_int_mod_def, integerTheory.INT_MOD_1] >>
  simp[]
QED



(* evaluate_subscript preserves toplevel_value_typed.
   Given a typed toplevel_value and subscript_type_ok, the result is typed
   at the subscript result type. Works for both INL (toplevel_value) and
   INR (storage ref) results. *)
Theorem evaluate_subscript_typed:
  !tenv arr_tv x idx x' ct it result_ty.
    evaluate_subscript tenv arr_tv x idx = INL x' /\
    toplevel_value_typed x arr_tv /\
    ~is_HashMapRef x /\
    subscript_type_ok ct it result_ty /\
    evaluate_type tenv ct = SOME arr_tv ==>
    ?rtv. evaluate_type tenv result_ty = SOME rtv /\
          (case x' of
           | INL tv => toplevel_value_typed tv rtv
           | INR (is_trans, slot, tv) => tv = rtv)
Proof
  rpt gen_tac >> Cases_on `x` >>
  simp[toplevel_value_typed_def, is_HashMapRef_def]
  (* Value v *)
  >- (Cases_on `v` >> Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac subscript_type_ok_evaluate >>
      Cases_on `evaluate_type tenv result_ty` >> gvs[] >>
      simp[toplevel_value_typed_def] >>
      drule_all evaluate_subscript_value_well_typed >> simp[])
  (* ArrayRef: arr_tv = ArrayTV elem_tv bd *)
  >> (Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `ct` >> gvs[subscript_type_ok_def] >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      simp[toplevel_value_typed_def])
QED


(* --- AugAssign helper: Update base case preserves value_has_type --- *)

(* evaluate_type tenv ty = SOME (BaseTV bt) ==> ty = BaseT bt *)
Theorem evaluate_type_BaseTV[local]:
  !tenv ty bt.
    evaluate_type tenv ty = SOME (BaseTV bt) ==> ty = BaseT bt
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp_tac (srw_ss()) [evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[]
QED

(* Helper: type_to_int_bound matches evaluate_type for int types *)
Theorem type_to_int_bound_evaluate_type[local]:
  !tenv ty leaf_tv.
    evaluate_type tenv ty = SOME leaf_tv ==>
    (!m. leaf_tv = BaseTV (UintT m) ==>
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) = Unsigned m) /\
    (!m. leaf_tv = BaseTV (IntT m) ==>
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) = Signed m)
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp_tac (srw_ss()) [evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[type_to_int_bound_def]
QED

(* Main helper: Update at leaf preserves value_has_type *)
Theorem update_base_preserves_vht:
  !ty bop nv la lv leaf_tv tenv et.
    assign_subscripts leaf_tv la [] (Update ty bop nv) = INL lv /\
    value_has_type leaf_tv la /\
    well_formed_type_value leaf_tv /\
    evaluate_type tenv ty = SOME leaf_tv /\
    well_typed_binop ty bop ty et /\
    (et = ty ==> value_has_type leaf_tv nv) ==>
    value_has_type leaf_tv lv
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [assign_subscripts_def] >> strip_tac >>
  imp_res_tac type_to_int_bound_evaluate_type >>
  Cases_on `bop` >> gvs[well_typed_binop_def] >>
  (* Resolve evaluate_type where ty is concrete *)
  TRY (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
       simp_tac (srw_ss()) [evaluate_type_def] >> strip_tac >> gvs[]) >>
  (* Simplify type_to_int_bound in evaluate_binop *)
  qpat_x_assum `evaluate_binop _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [type_to_int_bound_def] >> strip_tac >>
  (* BoolT: comparisons and membership return BoolV *)
  TRY (qpat_x_assum `value_has_type (BaseTV BoolT) la`
         (strip_assume_tac o REWRITE_RULE[value_has_type_def]) >>
       gvs[evaluate_binop_def, binop_negate_def, AllCaseEqs(),
           value_has_type_def] >> NO_TAC) >>
  (* Shift *)
  TRY (
    first_assum (mp_tac o MATCH_MP
      (evaluate_binop_shift_preserves_vht
       |> ONCE_REWRITE_RULE[CONJ_COMM]
       |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then (qspec_then `leaf_tv` mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    rpt CONJ_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  (* Arithmetic/bitwise: evaluate_binop_preserves_vht *)
  first_assum (mp_tac o MATCH_MP
    (REWRITE_RULE[GSYM AND_IMP_INTRO] evaluate_binop_preserves_vht)) >>
  TRY (disch_then match_mp_tac >>
       simp_tac (srw_ss()) [] >> rpt strip_tac >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  (* DecimalT/ExpMod/NotIn/NotEq: strip and simplify *)
  strip_tac >> simp[] >>
  (* NotIn/NotEq: evaluate_binop on BoolV returns BoolV *)
  Cases_on `la` >> gvs[value_has_type_def] >>
  gvs[evaluate_binop_def, AllCaseEqs()] >>
  Cases_on `nv` >> gvs[binop_negate_def, value_has_type_def, AllCaseEqs()]
QED


(* ---- default_value typing ---- *)

(* default_value is well-typed when tv comes from evaluate_type *)

Theorem evaluate_types_length[local]:
  !tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs ==>
    LENGTH tvs = LENGTH acc + LENGTH ts
Proof
  Induct_on `ts` >>
  simp[evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> res_tac >> gvs[ADD1]
QED

(* Helper: values_have_types self-default *)
Theorem values_have_types_default[local]:
  !tvs. EVERY (\tv. value_has_type tv (default_value tv)) tvs ==>
        values_have_types tvs (MAP default_value tvs)
Proof
  Induct >> simp[value_has_type_def]
QED

(* Helper: struct_has_type self-default *)
Theorem struct_has_type_default[local]:
  !args. EVERY (\(id,tv). value_has_type tv (default_value tv)) args ==>
         struct_has_type args (MAP (\(id,tv). (id, default_value tv)) args)
Proof
  Induct >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def]
QED

Theorem default_value_has_type:
  (!tenv typ tv.
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv (default_value tv)) /\
  (!tenv ts acc tvs.
    evaluate_types tenv ts acc = SOME tvs ==>
    EVERY (\tv. value_has_type tv (default_value tv)) acc ==>
    EVERY (\tv. value_has_type tv (default_value tv)) tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  (* BaseT *)
  >- (Cases_on `bt` >>
      simp[evaluate_type_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[default_value_def, value_has_type_def,
           within_int_bound_def] >>
      TRY (Cases_on `b`) >>
      gvs[evaluate_type_def, AllCaseEqs(), default_value_def,
           value_has_type_def, within_int_bound_def])
  (* TupleT *)
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >> gvs[default_value_def, default_value_tuple_MAP,
        value_has_type_def] >>
      irule values_have_types_default >> first_x_assum irule >> simp[])
  (* ArrayT *)
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `bd` >> gvs[default_value_def, value_has_type_def])
  (* StructT *)
  >- (strip_tac >> rpt gen_tac >>
      simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >> gvs[default_value_def, default_value_struct_MAP,
        value_has_type_def] >>
      irule struct_has_type_default >>
      `LENGTH args = LENGTH tvs` by
        (imp_res_tac evaluate_types_length >> gvs[]) >>
      gvs[EVERY_MEM, FORALL_PROD, MEM_ZIP, PULL_EXISTS, MEM_EL,
          EL_ZIP, EL_MAP, LENGTH_MAP])
  (* FlagT *)
  >- (simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[default_value_def, value_has_type_def])
  (* NoneT *)
  >- (simp[evaluate_type_def] >> rpt strip_tac >>
      gvs[default_value_def, value_has_type_def])
  (* evaluate_types nil *)
  >- (simp[evaluate_type_def] >> rpt strip_tac >> gvs[])
  (* evaluate_types cons *)
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> disch_then irule >>
      first_x_assum drule >> simp[])
QED

val default_value_has_type_thm = cj 1 default_value_has_type;

(* ---- evaluate_max_value / evaluate_min_value typing ---- *)

Theorem evaluate_max_value_well_typed:
  !typ tv. evaluate_type tenv typ = SOME tv /\
           evaluate_max_value typ = INL v ==>
           value_has_type tv v
Proof
  Cases >> simp[evaluate_max_value_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_max_value_def, evaluate_type_def,
                        AllCaseEqs(), value_has_type_def,
                        within_int_bound_def] >>
  rpt strip_tac >> gvs[value_has_type_def, within_int_bound_def] >>
  `1 <= 2 ** n /\ 1 <= 2 ** (n - 1)` by simp[ONE_LE_EXP] >>
  simp[integerTheory.INT_SUB, integerTheory.NUM_OF_INT]
QED

Theorem evaluate_min_value_well_typed:
  !typ tv. evaluate_type tenv typ = SOME tv /\
           evaluate_min_value typ = INL v ==>
           value_has_type tv v
Proof
  Cases >> simp[evaluate_min_value_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_min_value_def, evaluate_type_def,
                        AllCaseEqs(), value_has_type_def,
                        within_int_bound_def]
QED

(* ---- evaluate_convert typing ---- *)

Theorem evaluate_convert_well_typed:
  !v typ v' tenv tv.
    evaluate_convert v typ = INL v' /\
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv v'
Proof
  ho_match_mp_tac evaluate_convert_ind >>
  rpt strip_tac >>
  gvs[evaluate_convert_def, AllCaseEqs(), evaluate_type_def,
      value_has_type_def, bounded_decimal_op_def,
      within_int_bound_def, compatible_bound_def] >>
  gvs[LENGTH_TAKE, listTheory.PAD_RIGHT,
      LENGTH_word_to_bytes, word_to_bytes_be_def] >>
  TRY (Cases_on `b` >> gvs[ONE_LT_EXP])
QED

(* ---- evaluate_extract32 typing ---- *)

Theorem evaluate_extract32_well_typed:
  !bs n bt v tenv tv.
    evaluate_extract32 bs n bt = INL v /\
    evaluate_type tenv (BaseT bt) = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_extract32_def, AllCaseEqs()] >>
  TRY (drule evaluate_convert_well_typed >>
       disch_then (qspecl_then [`tenv`, `tv`] mp_tac) >>
       simp[evaluate_type_def, AllCaseEqs()] >> NO_TAC) >>
  gvs[value_has_type_def, evaluate_type_def, AllCaseEqs(),
      LENGTH_TAKE, LENGTH_DROP]
QED

(* ---- abi_to_vyper typing ---- *)

Theorem OPT_MMAP_LIST_REL[local]:
  !f xs ys. OPT_MMAP f xs = SOME ys ==>
    LIST_REL (\x y. f x = SOME y) xs ys
Proof
  Induct_on `xs` >> simp[OPT_MMAP_def] >>
  rpt strip_tac >> BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Theorem evaluate_types_LIST_REL[local]:
  !tenv ts tvs. evaluate_types tenv ts [] = SOME tvs ==>
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs
Proof
  rpt strip_tac >> gvs[evaluate_types_OPT_MMAP] >>
  irule OPT_MMAP_LIST_REL >> simp[]
QED

Theorem values_have_types_REPLICATE_inv[local]:
  !n tv vs. values_have_types (REPLICATE n tv) vs ==>
    all_have_type tv vs /\ LENGTH vs = n
Proof
  Induct >> simp[value_has_type_def] >>
  Cases_on `vs` >> simp[value_has_type_def] >> metis_tac[]
QED

Theorem struct_has_type_ZIP[local]:
  !names tvs vs. values_have_types tvs vs /\ LENGTH names = LENGTH tvs ==>
    struct_has_type (ZIP(names,tvs)) (ZIP(names,vs))
Proof
  Induct >> rpt gen_tac >>
  (Cases_on `tvs` >> Cases_on `vs` >> simp[value_has_type_def]) >>
  strip_tac >> gvs[]
QED

(* Helper for the list case: element-wise well-typing *)
Theorem abi_to_vyper_well_typed:
  (!tenv typ av v tv.
    abi_to_vyper tenv typ av = SOME v /\
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv v) /\
  (!tenv ts avs vs tvs.
    abi_to_vyper_list tenv ts avs = SOME vs /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs ==>
    values_have_types tvs vs)
Proof
  ho_match_mp_tac abi_to_vyper_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[abi_to_vyper_def, AllCaseEqs(), PULL_EXISTS]
  (* Bulk solver for base types, NoneT, FlagT *)
  >> TRY (simp[evaluate_type_def, AllCaseEqs(), check_IntV_def,
               value_has_type_def, within_int_bound_def,
               compatible_bound_def, integerTheory.INT_OF_NUM,
               integerTheory.NUM_OF_INT, LET_THM] >>
          rpt strip_tac >>
          gvs[value_has_type_def, within_int_bound_def,
              compatible_bound_def] >> NO_TAC)
  (* list nil/cons *)
  >> TRY (simp[value_has_type_def] >> NO_TAC)
  >> TRY (rpt strip_tac >> gvs[value_has_type_def] >> NO_TAC)
  (* TupleT *)
  >> TRY (strip_tac >> rpt gen_tac >>
          simp[evaluate_type_def, AllCaseEqs(), LET_THM] >>
          rpt strip_tac >> gvs[value_has_type_def] >>
          first_x_assum irule >> simp[] >>
          irule evaluate_types_LIST_REL >> simp[] >> NO_TAC)
  (* Remaining: ArrayT and StructT — common unfold + dispatch *)
  >> rpt strip_tac >>
  qpat_x_assum `evaluate_type _ _ = SOME _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [evaluate_type_def, AllCaseEqs(), LET_THM]) >>
  gvs[value_has_type_def]
  (* ArrayT *)
  >- (first_x_assum
        (qspec_then `REPLICATE (LENGTH avs) tv'` mp_tac) >>
      simp[rich_listTheory.LIST_REL_REPLICATE_same] >> strip_tac >>
      imp_res_tac values_have_types_REPLICATE_inv >>
      Cases_on `b` >>
      gvs[make_array_value_def, value_has_type_def, compatible_bound_def,
          enumerate_static_array_sorted, all_have_type_EVERY] >>
      irule sparse_has_type_enumerate >> simp[])
  (* StructT *)
  >> first_x_assum (qspec_then `tvs` mp_tac) >>
  simp[] >> (impl_tac >- (irule evaluate_types_LIST_REL >> simp[])) >>
  strip_tac >>
  irule struct_has_type_ZIP >>
  conj_tac >- (
    qpat_x_assum `evaluate_types _ _ _ = _` mp_tac >>
    simp[evaluate_types_OPT_MMAP] >> strip_tac >>
    imp_res_tac OPT_MMAP_LENGTH >> simp[LENGTH_MAP]) >>
  first_assum ACCEPT_TAC
QED

(* ---- evaluate_type_builtin typing (master lemma) ---- *)
(* AbiEncode excluded: it returns BytesV but typ describes the input data type.
   In well-typed programs, AbiEncode's ty ≠ target_ty, so the case is vacuous. *)

Theorem evaluate_type_builtin_well_typed:
  !cx tb typ vs v tv.
    tb <> AbiEncode /\
    evaluate_type_builtin cx tb typ vs = INL v /\
    evaluate_type (get_tenv cx) typ = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  Cases_on `tb` >> gvs[] >>
  (* Case-split vs deeply + value constructors to let def fire *)
  Cases_on `vs` >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
  TRY (Cases_on `t`) >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
  TRY (Cases_on `t'`) >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
  (* Case-split value constructors for Extract32/AbiDecode *)
  TRY (Cases_on `h`) >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
  TRY (Cases_on `h'`) >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
  TRY (Cases_on `typ`) >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
  (* Now only well-formed cases remain *)
  TRY (metis_tac[default_value_has_type |> cj 1]) >>
  TRY (metis_tac[evaluate_max_value_well_typed]) >>
  TRY (metis_tac[evaluate_min_value_well_typed]) >>
  TRY (metis_tac[evaluate_convert_well_typed]) >>
  TRY (metis_tac[evaluate_extract32_well_typed]) >>
  TRY (simp[evaluate_type_def, value_has_type_def,
            within_int_bound_def] >> NO_TAC) >>
  (* AbiDecode *)
  gvs[evaluate_abi_decode_def, AllCaseEqs(), LET_THM] >>
  TRY (metis_tac[abi_to_vyper_well_typed |> cj 1]) >>
  (* Remaining: Epsilon, FlagT/NoneT from AbiDecode *)
  gvs[evaluate_type_def, AllCaseEqs(), value_has_type_def,
      within_int_bound_def, LET_THM]
QED

(* evaluate_abi_decode produces well-typed values *)
Theorem evaluate_abi_decode_well_typed:
  !tenv typ bs v tv.
    evaluate_abi_decode tenv typ bs = INL v /\
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_abi_decode_def, AllCaseEqs(), LET_THM] >>
  metis_tac[abi_to_vyper_well_typed |> cj 1]
QED

(* evaluate_abi_decode_return produces well-typed values *)
Theorem evaluate_abi_decode_return_well_typed:
  !tenv ret_type bs v tv.
    evaluate_abi_decode_return tenv ret_type bs = INL v /\
    evaluate_type tenv ret_type = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_abi_decode_return_def, AllCaseEqs(), LET_THM] >>
  TRY (metis_tac[evaluate_abi_decode_well_typed]) >>
  (* Wrap case: abi decode of TupleT [ret_type] gives TupleV [v] *)
  (* Wrap: evaluate_abi_decode (TupleT [ret_type]) = INL (TupleV [v]) *)
  `evaluate_type tenv (TupleT [ret_type]) = SOME (TupleTV [tv])` by (
    imp_res_tac (cj 1 evaluate_type_well_formed) >>
    imp_res_tac well_formed_type_value_slot_size >>
    gvs[evaluate_type_def, OPT_MMAP_def, type_slot_size_def,
        wordsTheory.dimword_def]) >>
  drule_all evaluate_abi_decode_well_typed >> strip_tac >>
  gvs[value_has_type_inv, value_has_type_def]
QED

(* ===== IntCall finally: cleanup preserves state_well_typed ===== *)

(* The IntCall cleanup block: pop_function prev; conditional release.
   Preserves state_well_typed if prev has scope_well_typed scopes. *)
Theorem intcall_cleanup_preserves_swt:
  !prev nr is_view slot_opt target s r' s'.
    state_well_typed s /\
    EVERY scope_well_typed prev /\
    (do
       pop_function prev;
       if nr /\ ~is_view then
         (case slot_opt of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock target slot)
       else return ()
     od) s = (r', s') ==>
    state_well_typed s'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def, pop_function_def, set_scopes_def,
       return_def] >>
  Cases_on `nr /\ ~is_view` >> simp[return_def]
  >- (Cases_on `slot_opt` >> simp[return_def]
      >- (strip_tac >> gvs[state_well_typed_def])
      >> strip_tac >>
         rename1 `release_nonreentrant_lock target slot
                    (s with scopes := prev) = _` >>
         `s'.scopes = prev` by (
           drule release_nonreentrant_lock_scopes >> simp[]) >>
         `s'.immutables = s.immutables` by (
           drule release_nonreentrant_lock_immutables >> simp[]) >>
         gvs[state_well_typed_def])
  >> strip_tac >> gvs[state_well_typed_def]
QED

(* The IntCall body block: try (eval_stmts cx' body; return NoneV) handle_function.
   Preserves state_well_typed if eval_stmts preserves it. *)
Theorem intcall_body_preserves_swt:
  !cx' body pushed_st r s.
    (try
       (do eval_stmts cx' body; return NoneV od)
       handle_function) pushed_st = (r, s) /\
    (!res s_body.
       eval_stmts cx' body pushed_st = (res, s_body) ==>
       state_well_typed s_body) ==>
    state_well_typed s
Proof
  rpt gen_tac >> strip_tac >>
  drule try_state >> strip_tac >>
  (* In both cases (INL/INR), decompose the do-block to get eval_stmts result *)
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `eval_stmts cx' body pushed_st` >>
  rename1 `eval_stmts _ _ _ = (res_body, st_body)` >>
  Cases_on `res_body` >> simp[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  (* Now s = st_body (either directly or via handle_function_state) *)
  TRY (first_x_assum (strip_assume_tac o MATCH_MP handle_function_state) >>
       gvs[]) >>
  metis_tac[]
QED

(* intcall_finally_preserves_swt: use intcall_body_preserves_swt +
   intcall_cleanup_preserves_swt + state_well_typed_finally directly
   in the IntCall proof. No combined helper needed. *)




(* ===== ExtCall chain helpers ===== *)

(* Pair bind: monad_bind on pair-returning computations *)
Theorem pair_bind_apply:
  monad_bind (ff : evaluation_state -> (('a # 'b) + exception) # evaluation_state)
            (UNCURRY (kk : 'a -> 'b -> evaluation_state -> ('c + exception) # evaluation_state))
            st0 =
  case ff st0 of
    (INL (a, b), s2) => kk a b s2
  | (INR e, s2) => (INR e, s2)
Proof
  simp[bind_def, UNCURRY_DEF] >> Cases_on `ff st0` >> Cases_on `q` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Triviality return_pair_bind:
  (case return (x:'a, y:'b) (st0:evaluation_state) of
    (INL (a,b), s2) => (kk:'a -> 'b -> evaluation_state -> ('c + exception) # evaluation_state) a b s2
  | (INR e, s2) => (INR e, s2)) = kk x y st0
Proof
  simp[return_def]
QED

Theorem well_typed_opt_SOME:
  well_typed_opt env (SOME e) <=> well_typed_expr env e
Proof
  simp[Once well_typed_expr_def]
QED

(* ExtCall chain: from if/else through to final result.
   The chain after check+lift_option_type in ExtCall.
   Takes swt+ec for post-eval_exprs state, P7 IH for drv as direct hypothesis.
   target_addr already extracted by earlier lift_option_type. *)
Theorem extcall_chain_preserves_swt:
  !cx env ret_type is_stat func_name arg_types drv
   (vs:value list) st_es res st'.
    state_well_typed st_es /\ env_consistent env cx st_es /\
    functions_well_typed cx /\ context_well_typed cx /\
    well_typed_opt env drv /\
    IS_SOME (evaluate_type (get_tenv cx) ret_type) /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (!e. drv = SOME e ==>
      !env' st0 res0 st0'.
        well_typed_expr env' e /\ env_consistent env' cx st0 /\
        state_well_typed st0 /\ functions_well_typed cx /\ context_well_typed cx /\
        eval_expr cx e st0 = (res0, st0') ==>
        state_well_typed st0' /\ env_consistent env' cx st0' /\
        !tv. res0 = INL tv ==>
          (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 toplevel_value_typed tv tyv) /\
          (!v st''. materialise cx tv st0' = (INL v, st'') ==>
             state_well_typed st'' /\ env_consistent env' cx st'' /\
             ?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                   value_has_type tyv v)) /\
    (do
       check (vs <> []) "ExtCall no target";
       target_addr <- lift_option_type (dest_AddressV (HD vs))
                        "ExtCall target not address";
       (value_opt, arg_vals) <-
         if is_stat then return (NONE, TL vs)
         else do
           check (TL vs <> []) "ExtCall no value";
           v <- lift_option_type (dest_NumV (HD (TL vs)))
                  "ExtCall value not int";
           return (SOME v, TL (TL vs))
         od;
       calldata <-
         lift_option
           (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
           "ExtCall build_calldata";
       accounts <- get_accounts;
       tStorage <- get_transient_storage;
       result <-
         lift_option
           (run_ext_call cx.txn.target target_addr calldata value_opt
              accounts tStorage (vyper_to_tx_params cx.txn))
           "ExtCall run failed";
       (λ(success, returnData, accounts', tStorage').
         do
           check success "ExtCall reverted";
           update_accounts (K accounts');
           update_transient (K tStorage');
           if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
           else do
             ret_val <- lift_sum_runtime
               (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
             return (Value ret_val)
           od
         od) result
     od) st_es = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    !tv. res = INL tv ==>
      (?tyv. evaluate_type (get_tenv cx) ret_type = SOME tyv /\
             toplevel_value_typed tv tyv) /\
      (!v st''. materialise cx tv st' = (INL v, st'') ==>
         state_well_typed st'' /\ env_consistent env cx st'' /\
         ?tyv. evaluate_type (get_tenv cx) ret_type = SOME tyv /\
               value_has_type tyv v)
Proof
  let
    val ect = BasicProvers.every_case_tac
    val extcall_tail_tac =
      gvs[bind_apply, lift_option_def, return_def, raise_def,
          get_accounts_def, get_transient_storage_def,
          check_def, assert_def, ignore_bind_apply,
          update_accounts_def, update_transient_def,
          lift_option_type_def] >>
      ect >> gvs[raise_def, return_def, bind_apply, assert_def,
          ignore_bind_apply, update_accounts_def, update_transient_def,
          lift_sum_runtime_def] >>
      rename1 `run_ext_call _ _ _ _ _ _ _ = SOME result_tup` >>
      PairCases_on `result_tup` >> gvs[] >>
      gvs[bind_apply, assert_def, ignore_bind_apply,
          update_accounts_def, update_transient_def, return_def, raise_def] >>
      Cases_on `result_tup0` >> gvs[raise_def] >>
      rename1 `env_consistent env cx mid_st` >>
      rename1 `run_ext_call _ _ _ _ mid_st.accounts mid_st.tStorage _ =
               SOME (T, returnData, new_accts, new_tstor)` >>
      `state_well_typed (mid_st with <|accounts := new_accts; tStorage := new_tstor|>) /\
       env_consistent env cx (mid_st with <|accounts := new_accts; tStorage := new_tstor|>)` by (
        irule tp_preserved_scopes_immutables >>
        qexists_tac `mid_st` >> simp[evaluation_state_component_equality]) >>
      Cases_on `returnData = [] ∧ IS_SOME drv` >| [
        ASM_REWRITE_TAC [] >>
        gvs[] >> strip_tac >>
        Cases_on `drv` >> gvs[] >>
        rename1 `well_typed_opt env (SOME drv_expr)` >>
        `well_typed_expr env drv_expr` by gvs[well_typed_opt_SOME] >>
        first_x_assum (qspecl_then [`env`,
          `mid_st with <|accounts := new_accts; tStorage := new_tstor|>`,
          `res`, `st'`] mp_tac) >>
        simp[] >> strip_tac >> gvs[] >>
        rpt strip_tac >| [
          first_x_assum (qspec_then `tv` mp_tac) >> simp[],
          first_x_assum (qspec_then `tv` mp_tac) >> simp[] >>
          disch_then drule >> strip_tac >>
          qexists_tac `tyv` >> gvs[]
        ],
        ASM_REWRITE_TAC [] >>
        simp_tac (srw_ss()) [bind_apply, return_def, raise_def, lift_sum_runtime_def] >>
        ect >> gvs[return_def, raise_def, bind_apply, materialise_def,
                   toplevel_value_typed_def] >>
        gvs[IS_SOME_EXISTS] >>
        imp_res_tac evaluate_abi_decode_return_well_typed >> metis_tac[]
      ]
  in
    rpt gen_tac >> strip_tac >>
    (* Unfold the entire chain including check + lift_option_type prefix *)
    qpat_x_assum `(do _ od) _ = _` mp_tac >>
    simp_tac (srw_ss()) [bind_apply, pair_bind_apply, check_def, assert_def,
      return_def, raise_def, lift_option_type_def, ignore_bind_apply] >>
    Cases_on `is_stat` >> ASM_REWRITE_TAC [] >>
    simp_tac (srw_ss()) [return_def, check_def, assert_def,
      bind_apply, raise_def, lift_option_type_def] >>
    strip_tac >> extcall_tail_tac
  end
QED


Theorem case_lift_option:
  (case (opt : 'a option) of NONE => raise e | SOME v => return v) s =
    (INL x, t) <=> opt = SOME x /\ t = s
Proof
  Cases_on `opt` >> simp_tac (srw_ss()) [return_def, raise_def] >> metis_tac[]
QED

(* Lock acquire conditional: scopes and immutables preserved *)
Theorem lock_acquire_cond_scopes_immutables:
  !nr slot_opt addr is_view s res s'.
    (if nr then
       case slot_opt of
         NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) s = (res, s') ==>
    s'.scopes = s.scopes /\ s'.immutables = s.immutables
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `nr` >> gvs[return_def] >>
  Cases_on `slot_opt` >> gvs[raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[]
QED

(* Lock release conditional: scopes and immutables preserved *)
Theorem lock_release_cond_scopes_immutables:
  !nr is_view slot_opt addr s res s'.
    (if nr /\ ~is_view then
       case slot_opt of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock addr slot
     else return ()) s = (res, s') ==>
    s'.scopes = s.scopes /\ s'.immutables = s.immutables
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `nr` >> gvs[return_def] >>
  Cases_on `is_view` >> gvs[return_def] >>
  Cases_on `slot_opt` >> gvs[return_def] >>
  imp_res_tac release_nonreentrant_lock_scopes >>
  imp_res_tac release_nonreentrant_lock_immutables >> gvs[]
QED

(* env_consistent preserved when scopes are the same and immutables
   type_values are monotonically preserved (weaker than scopes_immutables
   which requires exact immutables equality). Useful after function calls
   where the body may modify immutables but preserves their type_values. *)
Theorem env_consistent_immutables_ptv:
  !env cx st st'.
    env_consistent env cx st /\
    st'.scopes = st.scopes /\
    (!src id tv v.
       FLOOKUP (get_source_immutables src
         (case ALOOKUP st'.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ==>
       ?v'. FLOOKUP (get_source_immutables src
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v')) ==>
    env_consistent env cx st'
Proof
  rw[env_consistent_def]
  (* var_types: depends only on scopes, which are the same *)
  >- metis_tac[]
  (* global_types: uses current_module immutables *)
  >- (rename1 `FLOOKUP env.global_types id = SOME ty` >>
      first_x_assum (qspecl_then [`current_module cx`, `id`, `tv`, `v`] mp_tac) >>
      simp[] >> strip_tac >> res_tac)
  (* toplevel_types: StorageVarDecl *)
  >- res_tac
  (* toplevel_types: HashMapVarDecl *)
  >- res_tac
  (* toplevel_types: immutable *)
  >- (first_x_assum (qspecl_then [`src_id_opt`, `id`, `tv`, `v`] mp_tac) >>
      simp[] >> strip_tac >> res_tac)
  (* flag_members: no immutables dependency *)
  >> res_tac >> metis_tac[]
QED

(* ===== IntCall tail helpers ===== *)

(* safe_cast on NoneV can only produce NoneV with NoneTV *)
Theorem safe_cast_NoneV:
  !tv crv. safe_cast tv NoneV = SOME crv ==> tv = NoneTV /\ crv = NoneV
Proof
  Cases >> simp[safe_cast_def] >>
  TRY (Cases_on `b`) >> simp[] >>
  TRY (Cases_on `b0`) >> simp[] >>
  TRY (Cases_on `b'`) >> simp[]
QED

(* Decompose INL result of finally(try fn_m handle_function)(cleanup):
   either fn_m succeeded (rv = NoneV) or returned a value *)
Theorem finally_try_handle_success_rv:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv, st_final) ==>
    (rv = NoneV /\ (?st_bdy. fn_m pushed_st = (INL (), st_bdy))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v), st_bdy))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res, try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res, cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res, inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res, fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED

(* Combines bind_arguments_scope_well_typed + args_dflts_typing_to_el +
   fn_sigs_consistent unification for the IntCall chain_bind case *)
Theorem intcall_bind_scope_well_typed:
  bind_arguments tenv params (vs ++ dflt_vs) = SOME sc /\
  LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                        value_has_type tv v) vs args /\
  LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                        value_has_type tv v) dflt_vs needed_dflts /\
  MAP expr_type args = TAKE (LENGTH args) (MAP SND params) /\
  MAP expr_type needed_dflts = MAP SND (DROP (LENGTH args) params) /\
  LENGTH args + LENGTH needed_dflts = LENGTH params ==>
  scope_well_typed sc
Proof
  strip_tac >>
  drule (GEN_ALL bind_arguments_scope_well_typed) >>
  disch_then irule >>
  ho_match_mp_tac (GEN_ALL args_dflts_typing_to_el) >>
  qexistsl [`args`, `needed_dflts`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Directly connects fn_sigs lookup to lookup_callable param_types.
   Avoids unification of fresh existentials in Resume blocks. *)
Theorem fn_sigs_param_types:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt, fn_name) = SOME (param_types, ret_ty) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn_name ts =
    SOME (fm, nr, params, dflts, ret_ty', fn_body) ==>
  param_types = MAP SND params /\ ret_ty = ret_ty'
Proof
  rpt strip_tac >>
  gvs[fn_sigs_consistent_def] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(* Default args types align with param types after explicit args *)
Theorem dflts_drop_types_match:
  !x3 x2 es.
    MAP expr_type x3 = MAP SND (DROP (LENGTH x2 - LENGTH x3) x2) /\
    LENGTH es <= LENGTH x2 /\ LENGTH x2 <= LENGTH es + LENGTH x3 ==>
    MAP expr_type (DROP (LENGTH x3 - (LENGTH x2 - LENGTH es)) x3) =
    MAP SND (DROP (LENGTH es) x2)
Proof
  rpt strip_tac >>
  `LENGTH x3 <= LENGTH x2` by (
    `LENGTH (MAP expr_type x3) =
     LENGTH (MAP SND (DROP (LENGTH x2 - LENGTH x3) x2))` by metis_tac[] >>
    fs[LENGTH_MAP, LENGTH_DROP]) >>
  rewrite_tac [GEN_ALL MAP_DROP] >>
  qpat_x_assum `MAP expr_type _ = _` SUBST1_TAC >>
  simp[GEN_ALL MAP_DROP, DROP_DROP_T]
QED

(* Length of explicit + default args equals params *)
Theorem dflts_drop_length_match:
  !x3 x2 es.
    MAP expr_type x3 = MAP SND (DROP (LENGTH x2 - LENGTH x3) x2) /\
    LENGTH es <= LENGTH x2 /\ LENGTH x2 <= LENGTH es + LENGTH x3 ==>
    LENGTH es + LENGTH (DROP (LENGTH x3 - (LENGTH x2 - LENGTH es)) x3) =
    LENGTH x2
Proof
  rpt strip_tac >>
  `LENGTH x3 <= LENGTH x2` by (
    `LENGTH (MAP expr_type x3) =
     LENGTH (MAP SND (DROP (LENGTH x2 - LENGTH x3) x2))` by metis_tac[] >>
    fs[LENGTH_MAP, LENGTH_DROP]) >>
  simp[LENGTH_DROP]
QED

(* Nonreentrant lock acquisition succeeds for suitable state *)
Theorem acquire_nonreentrant_lock_succeeds:
  !addr slot is_view st.
    st.tStorage addr (n2w slot) <> 1w ==>
    ?st'. acquire_nonreentrant_lock addr slot is_view st = (INL (), st')
Proof
  rpt strip_tac >>
  simp[acquire_nonreentrant_lock_def, get_transient_storage_def,
       return_def, update_transient_def, bind_def, ignore_bind_def,
       raise_def, LET_THM, vfmStateTheory.lookup_storage_def,
       vfmExecutionTheory.lookup_transient_storage_def] >>
  Cases_on `is_view` >> simp[return_def, update_transient_def]
QED

(* Conditional nonreentrant lock acquisition succeeds when slot exists *)
Theorem lock_acquire_cond_succeeds:
  !nr slot_opt addr is_view.
    (nr ==> slot_opt <> NONE) ==>
    ?s t. (if nr then
             case slot_opt of
               NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock addr slot is_view
           else return ()) s = (INL (), t)
Proof
  rpt strip_tac >>
  Cases_on `nr`
  >- (Cases_on `slot_opt` >- fs[] >>
      rename1 `SOME slot` >>
      qexists `ARB with tStorage := \a s. (0w:256 word)` >>
      simp[acquire_nonreentrant_lock_def, get_transient_storage_def,
           return_def, update_transient_def, bind_def, ignore_bind_def,
           raise_def, LET_THM, vfmStateTheory.lookup_storage_def,
           vfmExecutionTheory.lookup_transient_storage_def] >>
      Cases_on `is_view` >> simp[return_def, update_transient_def]) >>
  qexists `ARB` >> simp[return_def]
QED

val _ = export_theory();
