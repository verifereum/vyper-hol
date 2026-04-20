(*
 * Type preservation proof for the Vyper interpreter.
 *
 * Definitions and helpers are in vyperTypeSoundnessHelpersScript.sml.
 * This file contains the type_preservation theorem.
 * Uses suspend/Resume/Finalise for each case of the mutual induction.
 *)

Theory vyperTypeSoundness
Ancestors
  pair list option rich_list vyperInterpreter vyperState
  vyperContext vyperStorage vyperValue vyperValueOperation
  vyperAST vyperMisc vyperStatePreservation vyperScopePreservation
  vyperLookup vyperImmutablesPreservation vyperEvalExprPreservesScopesDom
  vyperEvalPreservesScopes vyperEvalPreservesImmutablesDom
  vyperTyping vyperEncodeDecode vyperAssignPreservesType
  vyperTypeSoundnessDefs vyperTypeSoundnessHelpers vyperBuiltinTyping
Libs
  wordsLib

val () = (); (* TODO: workaround https://github.com/HOL-Theorem-Prover/HOL/issues/1898, remove when fixed *)

(* ===== ML bindings: fast conjunct access ===== *)

(* pure_op_not_return conjuncts *)
val [lift_option_type_not_return, lift_option_not_return,
     lift_sum_not_return, check_not_return, type_check_not_return,
     get_Value_not_return] = CONJUNCTS pure_op_not_return;

(* evaluate_no_return conjuncts *)
val eval_iterator_not_return = cj 3 evaluate_no_return;
val eval_target_not_return = cj 4 evaluate_no_return;
val eval_targets_not_return = cj 5 evaluate_no_return;
val eval_base_target_not_return = cj 6 evaluate_no_return;
val eval_expr_not_return = cj 8 evaluate_no_return;
val eval_exprs_not_return = cj 9 evaluate_no_return;

(* well_typed_expr conjuncts *)
val wte_Name = cj 1 well_typed_expr_def;
val wte_BareGlobalName = cj 2 well_typed_expr_def;
val wte_TopLevelName = cj 3 well_typed_expr_def;
val wte_FlagMember = cj 4 well_typed_expr_def;
val wte_IfExp = cj 5 well_typed_expr_def;
val wte_Literal = cj 6 well_typed_expr_def;
val wte_StructLit = cj 7 well_typed_expr_def;
val wte_Subscript = cj 8 well_typed_expr_def;
val wte_Attribute = cj 9 well_typed_expr_def;
val wte_Builtin = cj 10 well_typed_expr_def;
val wte_TypeBuiltin = cj 11 well_typed_expr_def;
val wte_Pop = cj 12 well_typed_expr_def;
val wte_IntCall = cj 13 well_typed_expr_def;
val wte_ExtCall = cj 14 well_typed_expr_def;
val wte_Send = cj 15 well_typed_expr_def;
val wte_RawCallTarget = cj 16 well_typed_expr_def;
val wte_RawLog = cj 17 well_typed_expr_def;
val wte_RawRevert = cj 18 well_typed_expr_def;
val wte_SelfDestructTarget = cj 19 well_typed_expr_def;
val wte_CreateTarget = cj 20 well_typed_expr_def;
val wte_SubscriptTarget = cj 24 well_typed_expr_def;
val wte_AttributeTarget = cj 25 well_typed_expr_def;
val wte_exprs_cons = cj 27 well_typed_expr_def;
val wte_named_exprs_cons = cj 31 well_typed_expr_def;

(* evaluate_def conjuncts *)
val ev_Pass          = cj 1 evaluate_def;
val ev_Continue      = cj 2 evaluate_def;
val ev_Break         = cj 3 evaluate_def;
val ev_ReturnNone    = cj 4 evaluate_def;
val ev_ReturnSome    = cj 5 evaluate_def;
val ev_Raise1        = cj 6 evaluate_def;
val ev_Raise2        = cj 7 evaluate_def;
val ev_Raise3        = cj 8 evaluate_def;
val ev_Assert1       = cj 9 evaluate_def;
val ev_Assert2       = cj 10 evaluate_def;
val ev_Assert3       = cj 11 evaluate_def;
val ev_Log           = cj 12 evaluate_def;
val ev_AnnAssign     = cj 13 evaluate_def;
val ev_Append        = cj 14 evaluate_def;
val ev_Assign        = cj 15 evaluate_def;
val ev_AugAssign     = cj 16 evaluate_def;
val ev_If            = cj 17 evaluate_def;
val ev_For           = cj 18 evaluate_def;
val ev_Expr          = cj 19 evaluate_def;
val ev_stmts_nil     = cj 20 evaluate_def;
val ev_stmts_cons    = cj 21 evaluate_def;
val ev_Array         = cj 22 evaluate_def;
val ev_Range         = cj 23 evaluate_def;
val ev_BaseTarget    = cj 24 evaluate_def;
val ev_TupleTarget   = cj 25 evaluate_def;
val ev_targets_nil   = cj 26 evaluate_def;
val ev_targets_cons  = cj 27 evaluate_def;
val ev_NameTarget           = cj 28 evaluate_def;
val ev_BareGlobalNameTarget = cj 29 evaluate_def;
val ev_TopLevelNameTarget   = cj 30 evaluate_def;
val ev_AttributeTarget      = cj 31 evaluate_def;
val ev_SubscriptTarget      = cj 32 evaluate_def;
val ev_for_nil       = cj 33 evaluate_def;
val ev_for_cons      = cj 34 evaluate_def;
val ev_Name          = cj 35 evaluate_def;
val ev_BareGlobalName = cj 36 evaluate_def;
val ev_TopLevelName  = cj 37 evaluate_def;
val ev_FlagMember    = cj 38 evaluate_def;
val ev_IfExp         = cj 39 evaluate_def;
val ev_Literal       = cj 40 evaluate_def;
val ev_StructLit     = cj 41 evaluate_def;
val ev_Subscript     = cj 42 evaluate_def;
val ev_Attribute     = cj 43 evaluate_def;
val ev_Builtin       = cj 44 evaluate_def;
val ev_Pop           = cj 45 evaluate_def;
val ev_TypeBuiltin   = cj 46 evaluate_def;
val ev_Send          = cj 47 evaluate_def;
val ev_ExtCall       = cj 48 evaluate_def;
val ev_IntCall       = cj 49 evaluate_def;
val ev_RawCallTarget = cj 50 evaluate_def;
val ev_RawLog        = cj 51 evaluate_def;
val ev_RawRevert     = cj 52 evaluate_def;
val ev_SelfDestructTarget = cj 53 evaluate_def;
val ev_CreateTarget  = cj 54 evaluate_def;
val ev_exprs_nil     = cj 55 evaluate_def;
val ev_exprs_cons    = cj 56 evaluate_def;

(* well_typed_stmt conjuncts *)
val wts_Expr = cj 4 well_typed_stmt_def;
val wts_ReturnSome = cj 6 well_typed_stmt_def;
val wts_Raise3 = cj 9 well_typed_stmt_def;
val wts_Assert1 = cj 10 well_typed_stmt_def;
val wts_Assert2 = cj 11 well_typed_stmt_def;
val wts_Assert3 = cj 12 well_typed_stmt_def;
val wts_Log = cj 13 well_typed_stmt_def;
val wts_AnnAssign = cj 14 well_typed_stmt_def;
val wts_Append = cj 15 well_typed_stmt_def;
val wts_Assign = cj 16 well_typed_stmt_def;
val wts_AugAssign = cj 17 well_typed_stmt_def;
val wts_If = cj 18 well_typed_stmt_def;
val wts_For = cj 19 well_typed_stmt_def;

(* ===== Tactics ===== *)

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
  gvs[return_def, raise_def];

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
    TRY (irule tp_preserved_scopes_immutables >>
         rpt (first_x_assum (irule_at Any)) >> field_simp) >>
    TRY (irule state_well_typed_scopes_immutables >>
         first_x_assum (irule_at Any) >> field_simp) >>
    TRY (irule env_consistent_scopes_immutables >>
         rpt (first_x_assum (irule_at Any)) >> field_simp)
  end;
val swt_modify_tac = swt_modify_solve;

val not_return_tac =
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (imp_res_tac eval_expr_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac eval_exprs_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac eval_target_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac eval_targets_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac eval_base_target_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac eval_iterator_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac lift_option_type_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac lift_option_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac lift_sum_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac check_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac type_check_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac get_Value_not_return >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac materialise_error >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac (cj 1 assign_target_no_return) >> gvs[] >> NO_TAC) >>
  TRY (gvs[raise_def, return_def] >> NO_TAC);

(* Close error branch completely: resolve state, discharge swt+ec, then return *)
val tp_err_tac =
  rpt BasicProvers.VAR_EQ_TAC >>
  swt_resolve_state_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ASM_REWRITE_TAC[] >> not_return_tac;

val tp_peel_bind =
  PURE_ONCE_REWRITE_TAC[bind_def] >> simp_tac bool_ss [BETA_THM];

(* Normalize IH guards by expanding pure prefix operations *)
val IH_norm_thms =
  [check_def, type_check_def, lift_option_type_def,
   lift_option_def, return_def, raise_def, assert_def,
   AllCaseEqs(), PULL_EXISTS,
   bind_def, ignore_bind_def, UNCURRY, LET_THM];

(* Close error branch for pure prefix: state = st (no change) *)
val tp_pure_err_tac : tactic =
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_x_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [];

val tp_materialise_conclusion_tac =
  qpat_x_assum `!tv'. INL _ = INL tv' ==> _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  first_x_assum drule >> strip_tac;

val bind_apply = SIMP_RULE std_ss [FUN_EQ_THM] bind_def;
val ignore_bind_apply = SIMP_RULE std_ss [FUN_EQ_THM] ignore_bind_def;

(* Key iff lemmas for discharging guarded IH guards *)
val lift_option_type_INL = prove(
  ``!x str st v. lift_option_type x str st = (INL v, st) <=> x = SOME v``,
  Cases >> rw[lift_option_type_def, return_def, raise_def]);
val check_INL = prove(
  ``!b str st. check b str st = (INL (), st) <=> b``,
  Cases >> rw[check_def, return_def, raise_def, assert_def]);
val type_check_INL = prove(
  ``!b str st. type_check b str st = (INL (), st) <=> b``,
  Cases >> rw[type_check_def, return_def, raise_def, assert_def]);

(* Discharge a guarded IH by uncurrying its conjunction guard and
   repeatedly MATCH_MP-ing against assumptions.
   Usage: discharge_ih_tac mdefs ih_thm
   where mdefs are monadic definitions to expand in the guard,
   and ih_thm is the raw IH from evaluate_ind (in an SML fn binding).
   The result is mp_tac'd and strip_tac'd into assumptions. *)
(* Fully uncurry ALL conjunction guards at any nesting depth:
   (g1 /\ g2 ==> h1 /\ h2 ==> body) --> (g1 ==> g2 ==> h1 ==> h2 ==> body)
   Handles conjunctions separated by ==> at any depth. *)
fun FULL_UNCURRY_CONV tm =
  if is_imp tm then
    ((REWR_CONV (GSYM AND_IMP_INTRO) THENC RAND_CONV FULL_UNCURRY_CONV)
     ORELSEC (RAND_CONV FULL_UNCURRY_CONV))
    tm
  else ALL_CONV tm;

(* Discharge a guarded IH by:
   1. Expanding monadic defs in the guard with SIMP_RULE
   2. Fully uncurrying guard conjunction into separate implications
   3. SPEC_ALL + repeated MATCH_MP against assumptions
   4. Any remaining guard is discharged via impl_tac + gvs[]
   Result: the fully discharged IH body is mp_tac'd + strip_tac'd *)
fun discharge_ih_tac mdefs ih_thm : tactic = fn (asl, g) =>
  let
    val ih_simp = SIMP_RULE (srw_ss()) mdefs ih_thm
    val ih_curried = CONV_RULE (STRIP_QUANT_CONV FULL_UNCURRY_CONV) ih_simp
    val ih_spec = SPEC_ALL ih_curried
    fun try_all th [] = th
      | try_all th (a::rest) =
          (try_all (MATCH_MP th (ASSUME a)) rest
           handle HOL_ERR _ => try_all th rest)
    fun iterate th =
      let val th' = try_all th asl
      in if aconv (concl th') (concl th) then th else iterate th' end
      handle _ => th
    val ih_discharged = iterate ih_spec
    val _ = if is_imp (concl ih_discharged)
            then print ("discharge_ih_tac: REMAINING antecedent:\n" ^
                        term_to_string (fst (dest_imp (concl ih_discharged))) ^ "\n")
            else print "discharge_ih_tac: fully discharged!\n"
  in
    if is_imp (concl ih_discharged) then
      (mp_tac ih_discharged >>
       (impl_tac >- gvs[]) >>
       strip_tac) (asl, g)
    else
      (mp_tac ih_discharged >> strip_tac) (asl, g)
  end;

(* Core tactic for simple stmt cases: unfold, case-split, apply IHs.
   Uses AllCaseEqs to get all branches at once, then VAR_EQ_TAC + drule_all. *)
fun tp_stmt_no_return_tac ev_thm wts_thm extra_defs =
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_thm]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_thm] >>
  simp_tac (srw_ss())
    ([bind_apply, ignore_bind_apply, AllCaseEqs(),
      return_def, raise_def, BETA_THM] @ extra_defs) >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt (first_x_assum drule_all >> strip_tac) >>
  simp[] >>
  swt_resolve_state_tac >>
  TRY swt_modify_tac >>
  TRY not_return_tac;

(* Prove case-expanded = do-notation by simplifier normalization.
   Use: move case-expanded asm to goal via mp_tac, making goal
   `case_form = X ==> do_form = X`, then apply this. *)
val MONADIC_NORM_TAC = simp[bind_def, ignore_bind_def];

(* Convert !x1...xn. P(x1,...,xn) ==> Q  to  (?x1...xn. P(x1,...,xn)) ==> Q
   when none of xi are free in Q. Uses LEFT_FORALL_IMP_THM. *)
fun FORALLS_IMP_CONV tm =
  if is_forall tm then
    (QUANT_CONV FORALLS_IMP_CONV THENC HO_REWR_CONV LEFT_FORALL_IMP_THM) tm
  else REFL tm;

fun tp_chain_prefix_tac ev_thm wte_thm =
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[wte_thm] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_thm] >>
  simp_tac std_ss [bind_apply] >>
  Cases_on `eval_exprs cx es st` >> rename1 `(res_es, st1)` >>
  reverse (Cases_on `res_es`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rw[] >>
       qpat_x_assum `!env st res st'. well_typed_exprs _ _ /\ _ ==> _`
         drule_all >> simp[] >> NO_TAC) >>
  qpat_x_assum `!env st res st'. well_typed_exprs _ _ /\ _ ==> _`
    drule_all >> strip_tac;

val chain_scopes_thms =
  [push_log_scopes, update_accounts_scopes,
   update_transient_scopes, transfer_value_scopes];
val chain_immutables_thms =
  [push_log_immutables, update_accounts_immutables,
   update_transient_immutables, transfer_value_immutables];

(* Chain scopes/immutables preservation: peel binds one at a time *)
fun chain_scopes_imm_tac () = let
  val imp_chain = MAP_EVERY (TRY o imp_res_tac)
    (chain_scopes_thms @ chain_immutables_thms @
     [lift_option_type_state, lift_option_state, check_state,
      get_accounts_state, get_transient_storage_state])
  val peel_step =
    CHANGED_TAC (
      full_simp_tac std_ss [Once bind_apply, Once ignore_bind_apply,
                            COND_RATOR, LET_THM, UNCURRY]) >>
    imp_chain >> gvs[AllCaseEqs(), return_def, raise_def]
in
  rpt peel_step >> imp_chain >> gvs[return_def, raise_def]
end;

fun tp_chain_tail_tac value_tac =
  strip_tac >>
  `st'.scopes = st1.scopes /\ st'.immutables = st1.immutables` by
    chain_scopes_imm_tac () >>
  `state_well_typed st' /\ env_consistent env cx st'` by (
    irule tp_preserved_scopes_immutables >>
    qexists_tac `st1` >> gvs[]) >>
  simp[] >>
  TRY (rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC)) >>
  rpt strip_tac >>
  gvs[bind_apply, ignore_bind_apply, AllCaseEqs(),
      return_def, raise_def, COND_RATOR, LET_THM, UNCURRY,
      materialise_def, expr_type_def, evaluate_type_def,
      value_has_type_def, raw_call_return_type_def,
      toplevel_value_typed_def] >>
  value_tac;

val default_chain_value_tac =
  gvs[listTheory.LENGTH_TAKE_EQ] >>
  TRY (imp_res_tac (REWRITE_RULE [wordsTheory.dimword_def,
         EVAL ``2 ** dimindex(:256)``] bytes_slot_size_bound) >>
       gvs[] >> NO_TAC) >>
  TRY DECIDE_TAC;

fun tp_pure_base_target_tac ev_thm =
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_thm] >>
  simp[bind_def, return_def, raise_def,
       get_scopes_def, type_check_def, assert_def, check_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_type_def, LET_THM, ignore_bind_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[];

(* ===== eval_preserves_swt — master theorem ===== *)
(* Same as type_preservation but P2 includes value typing.           *)
(* type_preservation is derived from this at the end.                *)

Theorem eval_preserves_swt:
  (* Type soundness: well-typed programs never raise TypeError.
     Key insight: TypeError in the Vyper interpreter arises from:
     (1) materialise(HashMapRef) — blocked by ty <> NoneT in well_typed_expr
     (2) evaluate_binop type mismatches — blocked by well_typed_binop
     (3) evaluate_builtin type mismatches — blocked by well_typed_builtin_app
     (4) dest_XV failures after materialise — blocked by well_typed_expr + value_has_type
     (5) get_Value on non-Value toplevel_value — blocked by TopLevelName ty <> NoneT
     The no-TypeError conjunct for each case follows from IH + definition constraints.
     materialise_no_type_error bridges: if tv is well-typed (not NoneTV) then
     materialise doesn't produce TypeError. *)
  (* P0: eval_stmt — state + env preserved, no type errors, return well-typed *)
  (!cx s. !env ret_ty st res st'.
    well_typed_stmt env ret_ty s /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (* P1: eval_stmts — state + env preserved, no type errors, return well-typed *)
  (!cx ss. !env ret_ty st res st'.
    well_typed_stmts env ret_ty ss /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (* P2: eval_iterator — no type errors, value typing on success *)
  (!cx it. !env typ st res st'.
    well_typed_iterator env typ it /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!vs tyv. res = INL vs /\
              evaluate_type (get_tenv cx) typ = SOME tyv ==>
              EVERY (value_has_type tyv) vs)) /\
  (* P3: eval_target — no type errors *)
  (!cx g. !env st res st'.
    (?ty. well_typed_atarget env g ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_target cx g st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P4: eval_targets — no type errors *)
  (!cx gs. !env st res st'.
    EVERY (\g. ?ty. well_typed_atarget env g ty) gs /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_targets cx gs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P5: eval_base_target — no type errors *)
  (!cx bt. !env st res st'.
    (?ty. well_typed_target env bt ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P6: eval_for — no type errors, return well-typed *)
  (!cx tyv nm body vs. !env typ ret_ty st res st'.
    well_typed_stmts (env with var_types updated_by (flip FUPDATE (nm, typ)))
                     ret_ty body /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    nm NOTIN FDOM env.var_types /\
    eval_for cx tyv nm body vs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
               evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
               value_has_type ret_tv v)) /\
  (* P7: eval_expr — no type errors, typing on success *)
  (!cx e. !env st res st'.
    well_typed_expr env e /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_expr cx e st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!tv. res = INL tv ==>
       (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
              toplevel_value_typed tv tyv) /\
       (!v st''. materialise cx tv st' = (INL v, st'') ==>
          state_well_typed st'' /\ env_consistent env cx st'' /\
          (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv v)))) /\
  (* P8: eval_exprs — no type errors, typing on success *)
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!vs. res = INL vs ==>
      LIST_REL (\v e. ?tyv.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
        value_has_type tyv v) vs es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  (* P0 (19 cases) *)
  >- suspend "Pass"
  >- suspend "Continue"
  >- suspend "Break"
  >- suspend "ReturnNone"
  >- suspend "ReturnSome"
  >- suspend "Raise1"
  >- suspend "Raise2"
  >- suspend "Raise3"
  >- suspend "Assert1"
  >- suspend "Assert2"
  >- suspend "Assert3"
  >- suspend "Log"
  >- suspend "AnnAssign"
  >- suspend "Append"
  >- suspend "Assign"
  >- suspend "AugAssign"
  >- suspend "If"
  >- suspend "For"
  >- suspend "Expr"
  (* P1 (2 cases) *)
  >- suspend "stmts_nil"
  >- suspend "stmts_cons"
  (* P2 (2 cases) *)
  >- suspend "Array"
  >- suspend "Range"
  (* P3 (2 cases) *)
  >- suspend "BaseTarget"
  >- suspend "TupleTarget"
  (* P4 (2 cases) *)
  >- suspend "targets_nil"
  >- suspend "targets_cons"
  (* P5 (5 cases) *)
  >- suspend "NameTarget"
  >- suspend "BareGlobalNameTarget"
  >- suspend "TopLevelNameTarget"
  >- suspend "AttributeTarget"
  >- suspend "SubscriptTarget"
  (* P6 (2 cases) *)
  >- suspend "for_nil"
  >- suspend "for_cons"
  (* P7 (20 cases) *)
  >- suspend "Name"
  >- suspend "BareGlobalName"
  >- suspend "TopLevelName"
  >- suspend "FlagMember"
  >- suspend "IfExp"
  >- suspend "Literal"
  >- suspend "StructLit"
  >- suspend "Subscript"
  >- suspend "Attribute"
  >- suspend "Builtin"
  >- suspend "Pop"
  >- suspend "TypeBuiltin"
  >- suspend "Send"
  >- suspend "ExtCall"
  >- suspend "IntCall"
  >- suspend "RawCallTarget"
  >- suspend "RawLog"
  >- suspend "RawRevert"
  >- suspend "SelfDestructTarget"
  >- suspend "CreateTarget"
  (* P8 (2 cases) *)
  >- suspend "exprs_nil"
  >- suspend "exprs_cons"
QED

(* ===== Resume blocks: proved cases ===== *)

Resume eval_preserves_swt[Pass]:
  rpt gen_tac >> strip_tac >> gvs[ev_Pass, return_def, raise_def]
QED

Resume eval_preserves_swt[Continue]:
  rpt gen_tac >> strip_tac >> gvs[ev_Continue, return_def, raise_def]
QED

Resume eval_preserves_swt[Break]:
  rpt gen_tac >> strip_tac >> gvs[ev_Break, return_def, raise_def]
QED

Resume eval_preserves_swt[ReturnNone]:
  rpt gen_tac >> strip_tac >>
  gvs[ev_ReturnNone, return_def, raise_def,
      well_typed_stmt_def, Once evaluate_type_def, value_has_type_def]
QED

Resume eval_preserves_swt[ReturnSome]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[wts_ReturnSome] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_ReturnSome] >>
  simp[bind_def, AllCaseEqs(), raise_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `!env st res st'. well_typed_expr _ _ /\ _ ==> _`
    drule_all >> strip_tac >>
  TRY (gvs[] >>
       qpat_x_assum `!tv. INL _ = INL tv ==> _`
         (mp_tac o SIMP_RULE (srw_ss()) []) >>
       disch_then drule >> strip_tac >> gvs[] >> NO_TAC) >>
  gvs[] >>
  swt_resolve_state_tac >>
  rpt CONJ_TAC >>
  TRY not_return_tac >>
  TRY (imp_res_tac materialise_no_type_error >>
       gvs[toplevel_value_typed_def] >> NO_TAC) >>
  TRY (imp_res_tac materialise_error >> gvs[] >> NO_TAC) >>

QED

Resume eval_preserves_swt[Raise1]:
  gvs[ev_Raise1, raise_def]
QED

Resume eval_preserves_swt[Raise2]:
  gvs[ev_Raise2, raise_def]
QED

Resume eval_preserves_swt[Raise3]:
  tp_stmt_no_return_tac ev_Raise3 wts_Raise3 []
QED

Resume eval_preserves_swt[Assert1]:
  tp_stmt_no_return_tac ev_Assert1 wts_Assert1
    [switch_BoolV_def, COND_RATOR]
QED

Resume eval_preserves_swt[Assert2]:
  tp_stmt_no_return_tac ev_Assert2 wts_Assert2
    [switch_BoolV_def, COND_RATOR]
QED

Resume eval_preserves_swt[Log]:
  tp_stmt_no_return_tac ev_Log wts_Log [push_log_def]
QED

Resume eval_preserves_swt[Expr]:
  tp_stmt_no_return_tac ev_Expr wts_Expr
    [type_check_def, check_def, assert_def]
QED

Resume eval_preserves_swt[stmts_nil]:
  rpt gen_tac >> strip_tac >> gvs[ev_stmts_nil, return_def]
QED

Resume eval_preserves_swt[stmts_cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `well_typed_stmts env ret_ty (s1::ss)` >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[ev_stmts_cons, ignore_bind_apply] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  PURE_ONCE_REWRITE_TAC [ignore_bind_def] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `eval_stmt cx s1 st` >>
  rename1 `eval_stmt cx s1 st = (res_s, st_mid)` >>
  reverse (Cases_on `res_s`) >> simp_tac (srw_ss()) [] >>
  strip_tac >> gvs[] >>
  gvs[well_typed_stmt_def] >>
  (* P0 IH *)
  qpat_x_assum `!env' ret_ty' st'' res' st''. well_typed_stmt _ _ _ /\ _ ==> _`
    (qspecl_then [`env`, `ret_ty`, `st`] mp_tac) >> simp[] >>
  strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  (* P1 guarded IH *)
  qpat_x_assum `!s'' t. eval_stmt _ _ s'' = (INL (), t) ==> _`
    (qspecl_then [`st`, `st_mid`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`env`, `ret_ty`, `st_mid`] mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Resume eval_preserves_swt[BaseTarget]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def] >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_BaseTarget] >>
  simp[bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> gvs[return_def] >>
  first_x_assum (qspecl_then [`env`, `st`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >>
  strip_tac >> gvs[PAIR_FST_SND_EQ, return_def, UNCURRY]
QED

Resume eval_preserves_swt[TupleTarget]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def] >>
  `EVERY (\g. ?ty. well_typed_atarget env g ty) gs` by (
    qpat_x_assum `LIST_REL _ _ _` mp_tac >>
    rw[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_TupleTarget] >>
  simp[bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> gvs[return_def] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_preserves_swt[targets_nil]:
  rpt gen_tac >> strip_tac >> gvs[ev_targets_nil, return_def]
QED

Resume eval_preserves_swt[targets_cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[EVERY_DEF] >>
  qpat_x_assum `eval_targets _ (_::_) _ = _` mp_tac >>
  rewrite_tac[ev_targets_cons] >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `!env' st' res st''. _ /\ _ /\ _ /\ eval_target _ _ _ = _ ==> _`
    (qspecl_then [`env`, `st`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >>
  strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  qpat_x_assum `!s gv t. eval_target _ _ s = (INL gv, t) ==> _` drule >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[return_def]
QED

Resume eval_preserves_swt[NameTarget]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_NameTarget] >>
  simp[bind_def, return_def, raise_def,
       get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, LET_THM, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Resume eval_preserves_swt[BareGlobalNameTarget]:
  tp_pure_base_target_tac ev_BareGlobalNameTarget >>
  imp_res_tac lift_option_state >> gvs[] >>
  Cases_on `get_module_code cx (current_module cx)` >>
  gvs[return_def, raise_def]
QED

Resume eval_preserves_swt[TopLevelNameTarget]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_TopLevelNameTarget] >>
  simp[bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Resume eval_preserves_swt[AttributeTarget]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[wte_AttributeTarget] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_AttributeTarget] >>
  simp[bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> gvs[return_def, PAIR_FST_SND_EQ, UNCURRY] >>
  first_x_assum (qspec_then `env` mp_tac) >>
  simp[] >> disch_then match_mp_tac >> metis_tac[]
QED

Resume eval_preserves_swt[for_nil]:
  rpt gen_tac >> strip_tac >> gvs[ev_for_nil, return_def]
QED

Resume eval_preserves_swt[Name]:
  rpt gen_tac >> strip_tac >>
  fs[wte_Name] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Name] >>
  simp[bind_def, return_def, get_scopes_def, lift_option_type_def, LET_THM] >>
  Cases_on `lookup_scopes_val (string_to_num id) st.scopes` >>
  simp[raise_def] >>
  strip_tac >> gvs[] >>
  rpt strip_tac >>
  gvs[materialise_def, return_def, expr_type_def, toplevel_value_typed_def] >>
  `EVERY scope_well_typed st.scopes` by fs[state_well_typed_def] >>
  drule lookup_scopes_val_well_typed >> disch_then drule >>
  strip_tac >>
  qexists_tac `entry.type` >> simp[] >>
  fs[env_consistent_def] >> res_tac
QED

Resume eval_preserves_swt[Literal]:
  rpt gen_tac >> strip_tac >>
  fs[wte_Literal] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Literal] >> simp[return_def] >>
  strip_tac >> gvs[] >>
  rpt strip_tac >>
  gvs[materialise_def, return_def, expr_type_def, toplevel_value_typed_def] >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def] >>
  gvs[well_formed_type_def] >>
  `?tv. evaluate_type (get_tenv cx) v7 = SOME tv` by
    (Cases_on `evaluate_type (get_tenv cx) v7` >> gvs[]) >>
  qexists_tac `tv` >> simp[] >>
  irule evaluate_literal_has_type >>
  first_assum (irule_at (Pos last)) >> first_assum (irule_at Any)
QED

Resume eval_preserves_swt[exprs_nil]:
  rpt gen_tac >> strip_tac >> gvs[ev_exprs_nil, return_def]
QED

(* ===== Shared tactics for Resume blocks ===== *)

(* tp_p7_prefix_tac: common prefix for P7 expr proofs
   - strips IH and hypotheses
   - decomposes well_typed_expr
   - extracts env.type_defs = get_tenv cx
   - unfolds eval_expr definition *)
fun tp_p7_prefix_tac wte_thm ev_thm =
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_thm]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `env_consistent _ _ _` mp_tac >>
     simp_tac (srw_ss()) [env_consistent_def]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_thm] >>
  simp_tac std_ss [bind_apply, BETA_THM, LET_THM, ignore_bind_apply];

(* tp_materialise_bridge_tac: after get_Value x r = (INL x', r),
   establish materialise cx x r = (INL x', r) and apply IH *)
val tp_materialise_bridge_tac =
  `materialise cx x r = (INL x', r)` by
    (qpat_x_assum `get_Value _ _ = _` mp_tac >>
     Cases_on `x` >>
     simp_tac (srw_ss()) [get_Value_def, return_def, raise_def,
                          materialise_def]) >>
  first_x_assum drule >> strip_tac;

(* tp_bind_err_tac: dispatch error branch after Cases_on a bind step *)
val tp_bind_err_tac =
  strip_tac >>
  TRY (POP_ASSUM STRIP_ASSUME_TAC) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  TRY (imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac lift_option_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac lift_sum_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac check_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac type_check_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (imp_res_tac switch_BoolV_state >> rpt BasicProvers.VAR_EQ_TAC) >>
  TRY (first_x_assum drule_all >> strip_tac) >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  TRY (imp_res_tac eval_expr_not_return >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (imp_res_tac eval_exprs_not_return >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (imp_res_tac eval_target_not_return >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (imp_res_tac eval_targets_not_return >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (imp_res_tac eval_base_target_not_return >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (imp_res_tac eval_iterator_not_return >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (imp_res_tac materialise_error >>
       pop_assum mp_tac >> simp_tac (srw_ss()) []) >>
  TRY (first_assum ACCEPT_TAC);

Resume eval_preserves_swt[Assert3]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_Assert3]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Assert3] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Step 1: eval_expr cx e *)
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* Apply P7 IH for e *)
  first_x_assum drule_all >> strip_tac >>
  (* Step 2: switch_BoolV — True returns, False continues *)
  simp_tac (srw_ss()) [switch_BoolV_def, COND_RATOR, bind_apply, BETA_THM,
                        return_def] >>
  Cases_on `x = Value (BoolV T)` >> asm_simp_tac (srw_ss()) [return_def] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       simp_tac (srw_ss()) [] >> NO_TAC) >>
  (* False branch: need to case-split on BoolV F vs other *)
  Cases_on `x = Value (BoolV F)` >>
  asm_simp_tac (srw_ss()) [raise_def] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* BoolV F: eval_expr cx e' for reason string *)
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `eval_expr cx e' r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* Apply guarded IH for e' *)
  qpat_x_assum `!s'' tv t. eval_expr _ _ s'' = (INL tv, t) ==> _`
    (qspecl_then [`st`, `x`, `r`] mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then drule_all >> strip_tac >>
  (* get_Value *)
  simp_tac (srw_ss()) [get_Value_def, bind_apply, BETA_THM] >>
  Cases_on `x'` >> simp_tac (srw_ss()) [return_def, raise_def] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* lift_option_type (dest_StringV) + raise *)
  simp_tac (srw_ss()) [lift_option_type_def, bind_apply, BETA_THM] >>
  Cases_on `dest_StringV v` >>
  simp_tac (srw_ss()) [raise_def, return_def, bind_apply, BETA_THM] >>
  tp_bind_err_tac
QED

Resume eval_preserves_swt[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_AnnAssign]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `env_consistent _ _ _` mp_tac >>
     simp_tac (srw_ss()) [env_consistent_def]) >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (qpat_x_assum `well_formed_type _ _`
       (mp_tac o SIMP_RULE (srw_ss()) [well_formed_type_def]) >>
     ASM_REWRITE_TAC [] >> simp_tac (srw_ss()) [IS_SOME_EXISTS]) >>
  `well_formed_type_value tyv` by
    (qpat_assum `evaluate_type _ _ = SOME _`
       (ACCEPT_TAC o MATCH_MP (cj 1 evaluate_type_well_formed))) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac std_ss [ev_AnnAssign, LET_THM, bind_apply, BETA_THM,
                    lift_option_type_def, return_def] >>
  PURE_ONCE_ASM_REWRITE_TAC [] >>
  simp_tac std_ss [return_def, BETA_THM, bind_apply] >>
  (* Reduce the case (INL tyv, st) and re-bind *)
  simp_tac (srw_ss()) [] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Discharge guarded IH now (before case splits) *)
  first_x_assum (qspecl_then [`get_tenv cx`, `st`, `tyv`, `st`] mp_tac) >>
  simp_tac std_ss [lift_option_type_def, return_def] >>
  PURE_ONCE_ASM_REWRITE_TAC [] >>
  simp_tac std_ss [return_def] >> strip_tac >>
  (* eval_expr: case split *)
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  (* materialise: case split *)
  Cases_on `materialise cx x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
       strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       imp_res_tac materialise_error >> gvs[] >> NO_TAC) >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  tp_materialise_conclusion_tac >>
  `value_has_type tyv x'` by
    (qpat_x_assum `evaluate_type _ (expr_type e) = SOME _` mp_tac >>
     ASM_REWRITE_TAC [] >> strip_tac >> gvs[]) >>
  (* new_variable *)
  Cases_on `new_variable id tyv x' r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >>
  TRY (irule new_variable_swt >> metis_tac[] >> NO_TAC) >>
  TRY (irule new_variable_ec >> metis_tac[] >> NO_TAC) >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac new_variable_not_return >> gvs[]
QED

Resume eval_preserves_swt[Append]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Decompose well_typed_stmt for Append *)
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_Append]) >>
  (* Wrap well_typed_target as existential for P5 IH *)
  qpat_assum `well_typed_target env bt _`
    (fn th => ASSUME_TAC (Q.EXISTS (`?ty. well_typed_target env bt ty`,
                                    `ArrayT (expr_type e) bd`) th)) >>
  (* Unfold ev_Append *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Append] >>
  simp_tac std_ss [bind_apply, BETA_THM, UNCURRY] >>
  (* Step 1: eval_base_target cx bt st *)
  Cases_on `eval_base_target cx bt st` >> rename1 `(res_bt, st_bt)` >>
  reverse (Cases_on `res_bt`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  Cases_on `x` >> simp_tac (srw_ss()) [] >>
  rename1 `eval_base_target cx bt st = (INL (loc, sbs), st_bt)` >>
  (* P5 IH for eval_base_target *)
  first_x_assum drule_all >> strip_tac >>
  (* Step 2: eval_expr cx e st_bt *)
  Cases_on `eval_expr cx e st_bt` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       first_x_assum drule_all >> strip_tac >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> gvs[] >>
       imp_res_tac eval_expr_not_return >>
       first_x_assum (qspec_then `v` mp_tac) >>
       simp_tac (srw_ss()) [] >> NO_TAC) >>
  (* Apply guarded P7 IH for eval_expr *)
  qpat_x_assum `!s'' loc' sbs' t'. eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`st`, `loc`, `sbs`, `st_bt`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env' st0 res0 st0'. well_typed_expr _ _ /\ _ ==> _`
    (qspecl_then [`env`, `st_bt`, `INL x`, `r`] mp_tac) >>
  (impl_tac >- (rpt CONJ_TAC >> first_assum ACCEPT_TAC)) >> strip_tac >>
  (* Step 3: materialise cx x r *)
  Cases_on `materialise cx x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
       strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       imp_res_tac materialise_error >> gvs[] >> NO_TAC) >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  tp_materialise_conclusion_tac >>
  (* Step 4: assign_target cx (BaseTargetV loc sbs) (AppendOp x') r;
             return () *)
  simp_tac std_ss [bind_apply, BETA_THM, ignore_bind_apply] >>
  Cases_on `assign_target cx (BaseTargetV loc sbs) (AppendOp x') r` >>
  (* Apply assign_target_well_typed_ao BEFORE splitting result *)
  `state_well_typed r'' /\ env_consistent env cx r''` by
    suspend "Append_atwt" >>
  (* Now case-split the result *)
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac (cj 1 assign_target_no_return) >>
  first_x_assum (qspec_then `v` mp_tac) >> simp_tac (srw_ss()) []
QED

Theorem append_element_dynamic[local]:
  !tv a nv v.
    append_element tv a nv = INL v ==>
    ?elem_tv n. tv = ArrayTV elem_tv (Dynamic n)
Proof
  rpt gen_tac >>
  Cases_on `a` >> simp[append_element_def] >>
  Cases_on `a'` >> simp[append_element_def] >>
  Cases_on `tv` >> simp[append_element_def, AllCaseEqs()] >>
  Cases_on `b` >> simp[]
QED

Theorem assign_subscripts_append_dynamic[local]:
  !subs tv a nv v.
    assign_subscripts tv a subs (AppendOp nv) = INL v ==>
    ?elem_tv n. leaf_type tv subs = ArrayTV elem_tv (Dynamic n)
Proof
  Induct >- (
    rpt gen_tac >>
    simp[assign_subscripts_def, leaf_type_def] >>
    metis_tac[append_element_dynamic]
  ) >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `h` >> Cases_on `tv` >>
  simp_tac (srw_ss()) [Once assign_subscripts_def, AllCaseEqs(),
    LET_THM, PULL_EXISTS, leaf_type_def] >>
  rpt strip_tac >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  (* Remaining: AttrSubscript cases — need Cases_on a *)
  pop_assum mp_tac >>
  Cases_on `a` >>
  simp_tac (srw_ss()) [Once assign_subscripts_def, AllCaseEqs(),
    LET_THM, PULL_EXISTS] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `ALOOKUP l s` >> gvs[]
QED

Resume eval_preserves_swt[Append_atwt]:
  irule assign_target_well_typed_ao >>
  rpt (first_assum (irule_at Any)) >>
  rpt strip_tac >>
  (* Have: loc_type cx r loc tv, assign_subscripts tv a (REVERSE sbs) (AppendOp x') = INL v *)
  (* Use eval_base_target_type_connection to get leaf_type info *)
  drule eval_base_target_type_connection >> rpt (disch_then drule) >>
  strip_tac >>
  (* Now: evaluate_type (get_tenv cx) (ArrayT (expr_type e) bd) = SOME tyv',
          tyv' = leaf_type tv (REVERSE sbs), well_formed_type_value tv *)
  (* Use assign_subscripts_preserves_type *)
  irule assign_subscripts_preserves_type >>
  rpt (first_assum (irule_at Any)) >>
  rpt CONJ_TAC >>
  TRY (rpt strip_tac >> gvs[] >> NO_TAC) >>
  (* AppendOp condition: need leaf_type = ArrayTV _ (Dynamic _) *)
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule assign_subscripts_append_dynamic >> strip_tac >>
  qexistsl_tac [`elem_tv`, `n`] >>
  CONJ_TAC >- first_assum ACCEPT_TAC >>
  (* value_has_type elem_tv x': from leaf_type = ArrayTV tyv bd and
     leaf_type = ArrayTV elem_tv (Dynamic n), so elem_tv = tyv *)
  `evaluate_type (get_tenv cx) (ArrayT (expr_type e) bd) = SOME (leaf_type tv (REVERSE sbs))`
    by (first_assum ACCEPT_TAC) >>
  gvs[Once evaluate_type_def, AllCaseEqs()]
QED


Resume eval_preserves_swt[Assign]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Decompose well_typed_stmt for Assign *)
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_Assign]) >>
  (* Wrap well_typed_atarget as existential for P3 IH *)
  qpat_assum `well_typed_atarget env g (expr_type e)`
    (fn th => ASSUME_TAC (Q.EXISTS (`?ty. well_typed_atarget env g ty`,
                                    `expr_type e`) th)) >>
  (* Unfold ev_Assign *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Assign] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Step 1: eval_target cx g st *)
  Cases_on `eval_target cx g st` >> rename1 `(res_tgt, st_tgt)` >>
  reverse (Cases_on `res_tgt`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  rename1 `eval_target cx g st = (INL tgt_v, st_tgt)` >>
  (* P3 IH for eval_target *)
  first_x_assum drule_all >> strip_tac >>
  (* Discharge guarded P7 IH: specialise guard, then strip *)
  qpat_x_assum `!s'' gv t. eval_target _ _ _ = _ ==> _`
    (qspecl_then [`st`, `tgt_v`, `st_tgt`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* Step 2: eval_expr cx e st_tgt *)
  Cases_on `eval_expr cx e st_tgt` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       first_x_assum drule_all >> strip_tac >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> gvs[] >>
       imp_res_tac eval_expr_not_return >>
       first_x_assum (qspec_then `v` mp_tac) >>
       simp_tac (srw_ss()) [] >> NO_TAC) >>
  (* Apply P7 IH for eval_expr success *)
  qpat_x_assum `!env st res st'. well_typed_expr _ _ /\ _ ==> _`
    (qspecl_then [`env`, `st_tgt`, `INL x`, `r`] mp_tac) >>
  (impl_tac >- (rpt CONJ_TAC >> first_assum ACCEPT_TAC)) >> strip_tac >>
  (* Step 3: materialise cx x r *)
  Cases_on `materialise cx x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
       strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       imp_res_tac materialise_error >> gvs[] >> NO_TAC) >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  tp_materialise_conclusion_tac >>
  (* Step 4: assign_target cx tgt_v (Replace x') r; return () *)
  simp_tac std_ss [bind_apply, BETA_THM, ignore_bind_apply] >>
  Cases_on `assign_target cx tgt_v (Replace x') r` >>
  (* Apply assign_target_well_typed BEFORE splitting result *)
  `state_well_typed r'' /\ env_consistent env cx r''` by
    suspend "Assign_atwt" >>
  (* Now case-split the result *)
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac (cj 1 assign_target_no_return) >>
  first_x_assum (qspec_then `v` mp_tac) >> simp_tac (srw_ss()) []
QED

Resume eval_preserves_swt[Assign_atwt]:
  drule (cj 1 assign_target_well_typed) >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
  first_x_assum match_mp_tac >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `evaluate_type _ _ = SOME _`
    (fn th => qpat_assum `value_has_type _ _`
      (fn th2 => EXISTS_TAC (th |> concl |> rhs |> rand) >>
                 CONJ_TAC >| [ACCEPT_TAC th, ACCEPT_TAC th2]))
QED

Resume eval_preserves_swt[AugAssign]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Decompose well_typed_stmt for AugAssign *)
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_AugAssign]) >>
  (* Wrap well_typed_target as existential for P5 IH *)
  qpat_assum `well_typed_target env bt ty`
    (fn th => ASSUME_TAC (Q.EXISTS (`?ty'. well_typed_target env bt ty'`,
                                    `ty`) th)) >>
  (* Unfold ev_AugAssign *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_AugAssign] >>
  simp_tac std_ss [bind_apply, BETA_THM, UNCURRY, ignore_bind_apply] >>
  (* Step 1: eval_base_target cx bt st *)
  Cases_on `eval_base_target cx bt st` >> rename1 `(res_bt, st_bt)` >>
  reverse (Cases_on `res_bt`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  Cases_on `x` >> simp_tac (srw_ss()) [] >>
  rename1 `eval_base_target cx bt st = (INL (loc, sbs), st_bt)` >>
  (* P5 IH for eval_base_target *)
  first_x_assum drule_all >> strip_tac >>
  (* Step 2: eval_expr cx e st_bt *)
  Cases_on `eval_expr cx e st_bt` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       first_x_assum drule_all >> strip_tac >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> gvs[] >>
       imp_res_tac eval_expr_not_return >>
       first_x_assum (qspec_then `v` mp_tac) >>
       simp_tac (srw_ss()) [] >> NO_TAC) >>
  (* Apply guarded P7 IH for eval_expr *)
  qpat_x_assum `!s'' loc' sbs' t'. eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`st`, `loc`, `sbs`, `st_bt`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env' st0 res0 st0'. well_typed_expr _ _ /\ _ ==> _`
    (qspecl_then [`env`, `st_bt`, `INL x`, `r`] mp_tac) >>
  (impl_tac >- (rpt CONJ_TAC >> first_assum ACCEPT_TAC)) >> strip_tac >>
  (* Step 3: get_Value x r — state unchanged *)
  Cases_on `x` >> simp_tac (srw_ss()) [get_Value_def, return_def, raise_def] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  rename1 `eval_expr cx e st_bt = (INL (Value v_expr), r)` >>
  (* Step 4: assign_target cx (BaseTargetV loc sbs) (Update ty bop v_expr) r *)
  Cases_on `assign_target cx (BaseTargetV loc sbs) (Update ty bop v_expr) r` >>
  (* Apply assign_target_well_typed_ao BEFORE splitting result *)
  `state_well_typed r'' /\ env_consistent env cx r''` by
    suspend "AugAssign_atwt" >>
  (* Now case-split the result *)
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac (cj 1 assign_target_no_return) >>
  first_x_assum (qspec_then `v` mp_tac) >> simp_tac (srw_ss()) []
QED

Resume eval_preserves_swt[AugAssign_atwt]:
  irule assign_target_well_typed_ao >>
  rpt (first_assum (irule_at Any)) >>
  rpt strip_tac >>
  (* Have: loc_type cx r loc tv, assign_subscripts tv a (REVERSE sbs) (Update ty bop v_expr) = INL v *)
  drule eval_base_target_type_connection >> rpt (disch_then drule) >>
  strip_tac >>
  (* Now: evaluate_type (get_tenv cx) ty = SOME tyv',
          tyv' = leaf_type tv (REVERSE sbs), well_formed_type_value tv *)
  irule assign_subscripts_preserves_type >>
  rpt (first_assum (irule_at Any)) >>
  rpt CONJ_TAC >>
  TRY (rpt strip_tac >> gvs[] >> NO_TAC) >>
  (* Update condition: use update_base_preserves_vht *)
  rpt strip_tac >> gvs[] >>
  irule update_base_preserves_vht >>
  rpt (first_assum (irule_at Any)) >>
  CONJ_TAC >- (irule (cj 1 evaluate_type_well_formed) >>
               first_assum (irule_at Any)) >>
  strip_tac >> gvs[]
QED

Resume eval_preserves_swt[If]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_If]) >>
  (* Unfold ev_If *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_If] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Step 1: eval_expr cx e st *)
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* P7 IH for eval_expr *)
  first_x_assum drule_all >> strip_tac >>
  (* push_scope *)
  simp_tac (srw_ss()) [push_scope_def, return_def, bind_apply, BETA_THM] >>
  (* Discharge guarded P1 IHs (for ss and ss') *)
  qpat_x_assum `!s'' tv t s3 x0 t'. eval_expr _ _ s'' = _ /\ push_scope _ = _ ==>
    !env ret_ty st res st'. well_typed_stmts _ _ ss /\ _ ==> _`
    (qspecl_then [`st`, `x`, `r`, `r`, `()`, `r with scopes updated_by CONS FEMPTY`]
       mp_tac) >>
  simp_tac std_ss [push_scope_def, return_def] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!s'' tv t s3 x0 t'. eval_expr _ _ s'' = _ /\ push_scope _ = _ ==>
    !env ret_ty st res st'. well_typed_stmts _ _ ss' /\ _ ==> _`
    (qspecl_then [`st`, `x`, `r`, `r`, `()`, `r with scopes updated_by CONS FEMPTY`]
       mp_tac) >>
  simp_tac std_ss [push_scope_def, return_def] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* finally (switch_BoolV x (eval_stmts cx ss) (eval_stmts cx ss')) pop_scope *)
  simp_tac std_ss [finally_def, BETA_THM, bind_apply] >>
  simp_tac (srw_ss()) [switch_BoolV_def, COND_RATOR, bind_apply, BETA_THM] >>
  Cases_on `x = Value (BoolV T)` >> ASM_REWRITE_TAC [] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC
  >- suspend "If_True"
  >- suspend "If_False"
QED

Resume eval_preserves_swt[If_True]:
  (* Decompose: push_scope + finally eval_stmts pop_scope *)
  drule scope_bracket_decompose >> strip_tac >>
  (* Establish pushed-state well-typedness *)
  `state_well_typed (r with scopes updated_by CONS FEMPTY)` by (
    irule push_scope_swt >> first_assum ACCEPT_TAC) >>
  `env_consistent env cx (r with scopes updated_by CONS FEMPTY)` by (
    irule push_scope_ec >> first_assum ACCEPT_TAC) >>
  (* Apply P1 IH for ss *)
  qpat_x_assum `!env ret_ty st res st'. well_typed_stmts _ _ ss /\ _ ==> _`
    drule_all >> strip_tac >>
  (* Scope bracket preservation *)
  drule_all scope_bracket_preserves >> strip_tac >>
  (* Substitute st' = st_body with scopes := TL ... *)
  rpt BasicProvers.VAR_EQ_TAC >> ASM_REWRITE_TAC [] >>
  (* ReturnException typing: forward from IH (INL case trivial) *)
  rpt strip_tac >> Cases_on `q` >> gvs[]
QED

Resume eval_preserves_swt[If_False]:
  qpat_x_assum `do _ od _ = _` mp_tac >>
  Cases_on `x = Value (BoolV F)` >>
  ASM_REWRITE_TAC [] >>
  simp_tac (srw_ss()) [] >>
  strip_tac >- (
    (* BoolV F case: scope bracket pattern with ss' *)
    drule scope_bracket_decompose >> strip_tac >>
    `state_well_typed (r with scopes updated_by CONS FEMPTY)` by (
      irule push_scope_swt >> first_assum ACCEPT_TAC) >>
    `env_consistent env cx (r with scopes updated_by CONS FEMPTY)` by (
      irule push_scope_ec >> first_assum ACCEPT_TAC) >>
    qpat_x_assum `!env ret_ty st res st'. well_typed_stmts _ _ ss' /\ _ ==> _`
      drule_all >> strip_tac >>
    drule_all scope_bracket_preserves >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> ASM_REWRITE_TAC [] >>
    rpt strip_tac >> Cases_on `q` >> gvs[]) >>
  (* Error case: push+raise+pop gives (INR Error, r) *)
  qpat_x_assum `do _ od _ = _`
    (mp_tac o
     REWRITE_RULE [prove(``(r : evaluation_state) with scopes := r.scopes = r``,
                         simp[evaluation_state_component_equality])] o
     CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss())
       [push_scope_def, return_def, bind_apply, BETA_THM,
        finally_def, ignore_bind_apply, raise_def, pop_scope_def]))) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ASM_REWRITE_TAC [] >> simp_tac (srw_ss()) []
QED

Resume eval_preserves_swt[For]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_stmt _ _ (For _ _ _ _ _)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_For]) >>
  qpat_x_assum `eval_stmt _ (For _ _ _ _ _) _ = _` mp_tac >>
  rewrite_tac[ev_For] >>
  simp_tac std_ss [LET_THM, bind_apply, BETA_THM] >>
  (* Step 1: lift_option_type *)
  Cases_on `lift_option_type (evaluate_type (get_tenv cx) typ)
              "For evaluate_type" st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def] >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
    ASM_REWRITE_TAC [] >>
    rpt strip_tac >> imp_res_tac lift_option_type_not_return >>
    FULL_SIMP_TAC std_ss []) >>
  imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
  (* derive evaluate_type (get_tenv cx) typ = SOME x *)
  qpat_x_assum `lift_option_type _ _ _ = _` mp_tac >>
  PURE_REWRITE_TAC[lift_option_type_INL] >> strip_tac >>
  (* Discharge P2 IH guard *)
  first_x_assum (fn ih =>
    assume_tac (SIMP_RULE (srw_ss()) [lift_option_type_INL]
      (Q.SPECL [`get_tenv cx`, `r`, `x`, `r`] ih))) >>
  (* Step 2: eval_iterator *)
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `eval_iterator cx it r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def] >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> strip_tac >>
    ASM_REWRITE_TAC [] >>
    rpt strip_tac >>
    imp_res_tac (cj 3 evaluate_no_return) >>
    FULL_SIMP_TAC std_ss []) >>
  (* Apply P2 IH for success *)
  first_x_assum drule_all >> strip_tac >>
  (* Extract EVERY from P2 IH conclusion *)
  qpat_x_assum `!vs tyv. INL _ = INL vs /\ _ ==> _`
    (mp_tac o Q.SPECL [`x'`, `x`]) >>
  ASM_REWRITE_TAC [] >> strip_tac >>
  (* Step 3: unfold do-chain for check + eval_for *)
  simp_tac std_ss [bind_apply, ignore_bind_apply, BETA_THM] >>
  Cases_on `check (compatible_bound (Dynamic n) (LENGTH x'))
              "For too long" r''` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def]
  >- (
    (* check error branch *)
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac check_state >> rpt BasicProvers.VAR_EQ_TAC >>
    ASM_REWRITE_TAC [] >>
    rpt strip_tac >> imp_res_tac check_not_return >>
    FULL_SIMP_TAC std_ss [])
  >- (
    imp_res_tac check_state >>
    rpt BasicProvers.VAR_EQ_TAC >>
    strip_tac >>
    (* Derive compatible_bound from check *)
    qpat_x_assum `check _ _ _ = (INL _, _)` (fn th =>
      assume_tac (SIMP_RULE (srw_ss()) [check_INL] th)) >>
    (* Apply P6 IH *)
    last_x_assum mp_tac >>
    disch_then (mp_tac o
      SIMP_RULE (srw_ss()) [lift_option_type_INL, check_INL] o
      Q.SPECL [`get_tenv cx`, `r`, `x`, `r`,
                `r`, `x'`, `r'`, `r'`, `x''`, `r'`]) >>
    ASM_REWRITE_TAC [] >>
    disch_then drule_all >>
    simp_tac (srw_ss()) [])
QED
Resume eval_preserves_swt[Array]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Array] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def] >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> simp[]) >>
  (* eval_expr succeeded — apply P7 IH *)
  first_x_assum drule_all >> strip_tac >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `materialise cx x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def] >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac materialise_state >> gvs[]) >>
  (* materialise succeeded — get value typing from IH *)
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  strip_tac >>
  (* Remaining chain: lift_option_type x2, lift_option_type (extract_elements), return *)
  (* All pure — resolve directly *)
  (* The pure chain: lift_option_type resolves evaluate_type (known SOME),
     then case on extract_elements, then return. State unchanged = r. *)
  strip_tac >>
  gvs[lift_option_type_def, return_def, raise_def,
      pairTheory.pair_case_eq, CaseEq"sum", CaseEq"option"] >>
  (* Decompose evaluate_type (ArrayT typ bd) *)
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  simp_tac (srw_ss()) [evaluate_type_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> gvs[] >>
  (* Case split on extract_elements *)
  Cases_on `extract_elements (ArrayTV tv bd) x'` >>
  gvs[return_def, raise_def] >>
  irule extract_elements_well_typed >>
  `well_formed_type_value (ArrayTV tv bd)` by (
    irule (cj 1 evaluate_type_well_formed) >>
    qexists_tac `get_tenv cx` >> qexists_tac `ArrayT typ bd` >>
    simp[evaluate_type_def]) >>
  Cases_on `x'` >> gvs[value_has_type_def, extract_elements_def] >>
  metis_tac[]
QED

Resume eval_preserves_swt[Range]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Range] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def]
  >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    last_x_assum drule_all >> strip_tac >>
    ASM_REWRITE_TAC[] >> simp_tac (srw_ss()) [])
  >>
  last_x_assum drule_all >> strip_tac >>
  (* Step 2: get_Value tv1 *)
  Cases_on `get_Value x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def]
  >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
    ASM_REWRITE_TAC[] >> simp_tac (srw_ss()) [])
  >>
  imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Step 3: eval_expr cx e' r — instantiate guarded IH *)
  first_x_assum (qspecl_then [`st`, `x`, `r`, `r`, `x'`, `r`] mp_tac) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  Cases_on `eval_expr cx e' r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def]
  >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> strip_tac >>
    ASM_REWRITE_TAC[] >> simp_tac (srw_ss()) [])
  >>
  first_x_assum drule_all >> strip_tac >>
  (* Step 4: get_Value tv2 *)
  Cases_on `get_Value x'' r''` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def]
  >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
    ASM_REWRITE_TAC[] >> simp_tac (srw_ss()) [])
  >>
  imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Step 5: lift_sum (get_range_limits x' x'3') *)
  Cases_on `lift_sum (get_range_limits x' x'3') r'` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def]
  >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac lift_sum_state >> rpt BasicProvers.VAR_EQ_TAC >>
    ASM_REWRITE_TAC[] >> simp_tac (srw_ss()) [])
  >>
  imp_res_tac lift_sum_state >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Step 6: return — just LET + return, state = r' *)
  simp_tac (srw_ss()) [return_def, LET_THM] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  ASM_REWRITE_TAC[] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Extract materialise typing from e's IH: x is a toplevel_value,
     get_Value x r succeeded, so materialise cx x r gives same value *)
  qpat_x_assum `!tv. INL x = INL tv ==> _`
    (mp_tac o SIMP_RULE (srw_ss()) []) >>
  strip_tac >>
  qpat_x_assum `get_Value x r = _` mp_tac >>
  Cases_on `x` >> simp_tac (srw_ss()) [get_Value_def, return_def, raise_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `?tyv_e. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv_e /\
           value_has_type tyv_e v` by (
    first_x_assum (mp_tac o Q.SPEC `v`) >>
    PURE_REWRITE_TAC[materialise_Value] >>
    simp_tac (srw_ss()) []) >>
  (* Extract materialise typing from e''s IH *)
  qpat_x_assum `!tv. INL x'' = INL tv ==> _`
    (mp_tac o SIMP_RULE (srw_ss()) []) >>
  strip_tac >>
  qpat_x_assum `get_Value x'' _ = _` mp_tac >>
  Cases_on `x''` >> simp_tac (srw_ss()) [get_Value_def, return_def, raise_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `?tyv_e'. evaluate_type (get_tenv cx) (expr_type e') = SOME tyv_e' /\
            value_has_type tyv_e' v'` by (
    first_x_assum (mp_tac o Q.SPEC `v'`) >>
    PURE_REWRITE_TAC[materialise_Value] >>
    simp_tac (srw_ss()) []) >>
  (* Now unify types: expr_type e = expr_type e', so tyv_e = tyv_e' = tyv *)
  `tyv_e = tyv /\ tyv_e' = tyv` by
    (qpat_x_assum `expr_type e = _` (fn th => gvs[th])) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Extract get_range_limits from lift_sum *)
  qpat_x_assum `lift_sum _ _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [lift_sum_def, AllCaseEqs(), return_def, raise_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (srw_ss()) [] >>
  (* Case split v and v' to IntV — only IntV case survives *)
  Cases_on `v` >> Cases_on `v'` >>
  gvs[get_range_limits_def, return_def, raise_def] >>
  (* Remaining: v = IntV i, v' = IntV i'.
     Top assumption is the case expression from lift_sum.
     Need: i <= i' for get_range_limits to succeed *)
  first_x_assum mp_tac >>
  COND_CASES_TAC >>
  simp_tac (srw_ss()) [return_def, raise_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (srw_ss()) [] >>
  irule range_values_well_typed >>
  CONJ_TAC >- ASM_REWRITE_TAC[] >>
  Q.EXISTS_TAC `i'` >>
  simp_tac (srw_ss()) [get_range_limits_def] >>
  ASM_REWRITE_TAC[]
QED

Resume eval_preserves_swt[SubscriptTarget]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Decompose well_typed_target for SubscriptTarget *)
  qpat_x_assum `well_typed_target _ (SubscriptTarget _ _) _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_SubscriptTarget]) >>
  (* Wrap bt typing as existential for P5 IH matching — keep existential *)
  qpat_assum `well_typed_target env bt tgt_ty`
    (fn th => ASSUME_TAC (Q.EXISTS (`?ty. well_typed_target env bt ty`,
                                    `tgt_ty`) th)) >>
  (* Unfold eval_base_target *)
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  rewrite_tac[ev_SubscriptTarget] >>
  simp_tac std_ss [bind_apply, BETA_THM, UNCURRY] >>
  (* Step 1: eval_base_target cx bt st *)
  Cases_on `eval_base_target cx bt st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* P5 IH for bt *)
  first_x_assum drule_all >> strip_tac >>
  (* Decompose pair result *)
  Cases_on `x` >> simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Step 2: eval_expr cx e *)
  Cases_on `eval_expr cx e r` >>
  reverse (Cases_on `q'`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* P7 IH for e (guarded by eval_base_target success) *)
  qpat_x_assum `!s'' loc sbs t'. eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`st`, `q`, `r'`, `r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  (* Steps 3-5: get_Value + lift_option_type + return — state-preserving *)
  Cases_on `get_Value x r''` >>
  reverse (Cases_on `q'`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `lift_option_type (value_to_key x') "SubscriptTarget value_to_key" r''` >>
  reverse (Cases_on `q'`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> first_assum ACCEPT_TAC
QED

Theorem for_loop_scope_bracket_ec[local]:
  env_consistent (env with var_types updated_by flip $|+ (nm, typ)) cx st_body /\
  eval_stmts cx body (st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))) =
    (res_body, st_body) /\
  nm NOTIN FDOM env.var_types ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac >>
  `env_consistent env cx st_body` by (
    irule env_consistent_weaken_var_types >>
    qexists_tac `env with var_types updated_by flip FUPDATE (nm, typ)` >>
    ASM_REWRITE_TAC [] >>
    simp_tac (srw_ss()) [finite_mapTheory.FLOOKUP_UPDATE] >>
    rpt strip_tac >> Cases_on `nm = id` >> ASM_REWRITE_TAC [] >>
    rpt BasicProvers.VAR_EQ_TAC >> gvs[finite_mapTheory.FLOOKUP_DEF]) >>
  drule scope_bracket_preserves_ec >>
  disch_then drule >>
  (impl_tac >- (rpt strip_tac >> gvs[finite_mapTheory.FDOM_FUPDATE,
    finite_mapTheory.FDOM_FEMPTY])) >>
  simp[]
QED

Resume eval_preserves_swt[for_cons]:
  rpt gen_tac >> DISCH_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `EVERY _ (v::vs)` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `well_formed_type_value tyv` by (
    qpat_assum `evaluate_type _ _ = SOME tyv`
      (ACCEPT_TAC o MATCH_MP (cj 1 evaluate_type_well_formed))) >>
  (* Split the conjoined IHs *)
  qpat_x_assum `_ /\ _`
    (fn th => let val (p6ih, p1ih) = CONJ_PAIR th in
       ASSUME_TAC p6ih >> ASSUME_TAC p1ih end) >>
  (* Discharge P1 IH guard (push_scope_with_var always succeeds) *)
  qpat_x_assum `!s'' x t. push_scope_with_var _ _ _ _ = _ ==> _`
    (ASSUME_TAC o SIMP_RULE (srw_ss()) [push_scope_with_var_def, return_def]) >>
  (* Unfold eval_for and push_scope_with_var *)
  qpat_x_assum `eval_for _ _ _ _ (v::vs) _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [ev_for_cons, push_scope_with_var_def,
       return_def, bind_apply, ignore_bind_apply, BETA_THM]) >>
  (* Case split on the finally result *)
  Cases_on `finally (try do eval_stmts cx body; return F od
    handle_loop_exception) pop_scope
    (st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>)))` >>
  (* Apply for_body_decompose BEFORE case splitting q, to keep clauses *)
  drule for_body_decompose >> strip_tac >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Establish pushed state properties for P1 IH *)
  `state_well_typed (st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>)))` by (
    irule push_scope_with_var_swt >> ASM_REWRITE_TAC []) >>
  `env_consistent (env with var_types updated_by flip FUPDATE (nm, typ)) cx
     (st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>)))` by (
    irule push_scope_with_var_ec >> ASM_REWRITE_TAC []) >>
  (* P1 IH for eval_stmts body *)
  first_x_assum (qspecl_then
    [`env with var_types updated_by flip FUPDATE (nm, typ)`,
     `ret_ty`,
     `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))`,
     `res_body`, `st_body`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC []) >>
  strip_tac >>
  (* scope bracket preserves swt *)
  drule_all scope_bracket_preserves_swt >> strip_tac >>
  (* scope bracket preserves ec (weaken from extended env + pop scope) *)
  drule_all for_loop_scope_bracket_ec >> strip_tac >>
  ASM_REWRITE_TAC [] >>
  (* Two cases: INR (exception propagated) or INL (broke/continue) *)
  TRY (
    (* INR case: use reverse clause to get res_body = INR y *)
    qpat_x_assum `!e. INR _ = INR e ==> _`
      (ASSUME_TAC o SIMP_RULE (srw_ss()) []) >>
    rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum match_mp_tac >> ASM_REWRITE_TAC [] >> NO_TAC) >>
  (* INL case: x is the broke flag *)
  qpat_x_assum `!e. INL _ = INR e ==> _` (K ALL_TAC) >>
  Cases_on `x` >> simp_tac (srw_ss()) [return_def] >>
  (* Both goals: simplify the if-T/if-F assumption *)
  qpat_x_assum `(if _ then _ else _) _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [return_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* T case (break): trivially closed from assumptions *)
  TRY (ASM_REWRITE_TAC [] >> simp_tac (srw_ss()) [] >> NO_TAC) >>
  (* F case: recurse with P6 IH *)
  qpat_x_assum `!s'' x t s''' broke t'. _` (qspecl_then
    [`st`, `()`,
     `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))`,
     `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))`,
     `F`, `st_body with scopes := TL st_body.scopes`] mp_tac) >>
  simp_tac std_ss [push_scope_with_var_def, return_def] >>
  (impl_tac >- ASM_REWRITE_TAC []) >>
  disch_then drule_all >> strip_tac >>
  ASM_REWRITE_TAC []
QED

Resume eval_preserves_swt[BareGlobalName]:
  tp_p7_prefix_tac wte_BareGlobalName ev_BareGlobalName >>
  (* Step 1: get_immutables *)
  Cases_on `get_immutables cx (current_module cx) st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  imp_res_tac get_immutables_state >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Step 2: lift_option_type (FLOOKUP imms n) *)
  simp_tac (srw_ss()) [lift_option_type_def, bind_apply, BETA_THM, return_def] >>
  Cases_on `FLOOKUP x (string_to_num id)` >>
  simp_tac (srw_ss()) [raise_def, return_def] >>
  TRY (tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (* State preserved, env_consistent preserved *)
  ASM_REWRITE_TAC [] >>
  (* materialise (Value (SND x')) is trivial *)
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[materialise_Value, expr_type_def, toplevel_value_typed_def] >>
  (* Get value typing from get_immutables_well_typed *)
  drule get_immutables_well_typed >> (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `FLOOKUP imms _ = SOME tvv` >>
  Cases_on `tvv` >>
  first_x_assum drule >> strip_tac >>
  (* Get evaluate_type from env_consistent *)
  drule get_immutables_env_consistent_link >> strip_tac >>
  qpat_x_assum `env_consistent _ _ _` mp_tac >>
  simp_tac (srw_ss()) [env_consistent_def] >>
  strip_tac >> first_x_assum drule >>
  disch_then (mp_tac o Q.SPECL [`q`, `r'`]) >>
  qpat_x_assum `imms = _` (fn eq => REWRITE_TAC [GSYM eq]) >>
  PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac std_ss [] >> strip_tac >>
  first_assum ACCEPT_TAC
QED

Resume eval_preserves_swt[TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ (TopLevelName _ _)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_TopLevelName]) >>
  qpat_x_assum `eval_expr _ (TopLevelName _ _) _ = _` mp_tac >>
  rewrite_tac[ev_TopLevelName] >> strip_tac >>
  imp_res_tac lookup_global_state >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >> rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC
  (* 4 goals: tvt, swt, ec, vht; all after lookup_global + maybe materialise *)
  >- ((* toplevel_value_typed *)
      simp[expr_type_def] >>
      `?tyv. evaluate_type (get_tenv cx) vs = SOME tyv` by
        (gvs[well_formed_type_def, IS_SOME_EXISTS] >>
         metis_tac[env_consistent_type_defs]) >>
      qexists_tac `tyv` >> simp[] >>
      irule lookup_global_toplevel_typed >> metis_tac[])
  >> ((* materialise goals: swt, ec, vht *)
      imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
      simp[expr_type_def] >>
      irule lookup_global_materialise_well_typed >> metis_tac[])
QED

Resume eval_preserves_swt[FlagMember]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `nsid` >>
  qpat_x_assum `well_typed_expr _ (FlagMember _ _ _)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_FlagMember]) >>
  qpat_x_assum `eval_expr _ (FlagMember _ _ _) _ = _` mp_tac >>
  rewrite_tac[ev_FlagMember] >> strip_tac >>
  imp_res_tac eval_expr_FlagMember_state >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  (* Get flag info from env_consistent *)
  `?ts. get_module_code cx q = SOME ts /\
        lookup_flag r ts = SOME ls /\
        FLOOKUP (get_tenv cx) (string_to_num r) = SOME (FlagArgs (LENGTH ls))`
    by (gvs[env_consistent_def] >> res_tac) >>
  (* Resolve lookup_flag_mem to concrete value *)
  gvs[lookup_flag_mem_def, lift_option_type_def, return_def, raise_def,
      bind_def] >>
  `INDEX_OF mid ls <> NONE` by gvs[INDEX_OF_eq_NONE] >>
  Cases_on `INDEX_OF mid ls` >> gvs[] >>
  (* Now res = INL (Value (FlagV (2**x))), st' = st *)
  rpt strip_tac >> gvs[materialise_def, return_def, toplevel_value_typed_def] >>
  simp[expr_type_def, evaluate_type_def, LET_THM, value_has_type_def] >>
  imp_res_tac env_consistent_type_defs >>
  gvs[INDEX_OF_eq_SOME, well_formed_type_def, evaluate_type_def, LET_THM] >>
  `LENGTH ls <= 256` by (gvs[AllCaseEqs()] >> CCONTR_TAC >> gvs[])
QED

Resume eval_preserves_swt[IfExp]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ (IfExp _ _ _ _)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_IfExp]) >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  rewrite_tac[ev_IfExp] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Step 1: eval_expr cx e (cond) *)
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* Apply P7 IH for e *)
  qpat_x_assum `!env st res st'. well_typed_expr _ e /\ _ ==> _`
    drule_all >> strip_tac >>
  (* Step 2: switch_BoolV *)
  simp_tac (srw_ss()) [switch_BoolV_def, COND_RATOR, bind_apply, BETA_THM] >>
  Cases_on `x = Value (BoolV T)` >> ASM_REWRITE_TAC [] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC
  >- suspend "IfExp_True"
  >- suspend "IfExp_False"
QED

(* IfExp bridge: goal talks about expr_type (IfExp ...) but assumption
   talks about expr_type e'. Since expr_type (IfExp t ...) = t = expr_type e''
   and expr_type e' = expr_type e'', just rewrite and ACCEPT_TAC. *)
(* Rewrite goal: expr_type (IfExp t ...) → t, then match assumption *)
val ifexp_expr_type_thm = cj 5 expr_type_def;
(* Bridge: rewrite expr_type (IfExp t ...) -> t in goal, then ACCEPT_TAC
   if matching assumption available. For True branch: also rewrite via
   expr_type e' = expr_type e''. *)
fun tp_ifexp_bridge_tac () =
  CONV_TAC (DEPTH_CONV (REWR_CONV ifexp_expr_type_thm)) >>
  TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_type _ = expr_type _` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC;

Resume eval_preserves_swt[IfExp_True]:
  qpat_x_assum `!s'' tv t. eval_expr _ e _ = _ ==>
    !env st res st'. well_typed_expr _ e' /\ _ ==> _`
    (fn ih => mp_tac (ih |> Q.SPECL [`st`, `Value (BoolV T)`, `r`])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  tp_ifexp_bridge_tac ()
QED

Resume eval_preserves_swt[IfExp_False]:
  Cases_on `x = Value (BoolV F)` >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  ASM_REWRITE_TAC [] >>
  simp_tac (srw_ss()) [raise_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  TRY (rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       simp_tac (srw_ss()) [] >> NO_TAC) >>
  qpat_x_assum `!s'' tv t. eval_expr _ e _ = _ ==>
    !env st res st'. well_typed_expr _ e'' /\ _ ==> _`
    (fn ih => mp_tac (ih |> Q.SPECL [`st`, `Value (BoolV F)`, `r`])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  tp_ifexp_bridge_tac ()
QED
(* ===== Local helpers for P7 expr cases ===== *)

Theorem evaluate_type_StructT_is_StructTV[local]:
  !tenv id tv. evaluate_type tenv (StructT id) = SOME tv ==>
    ?ftypes. tv = StructTV ftypes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP]
QED

Theorem attribute_type_ok_evaluate[local]:
  !tenv sname field_id result_ty ftypes.
    attribute_type_ok tenv (StructT sname) field_id result_ty /\
    evaluate_type tenv (StructT sname) = SOME (StructTV ftypes) ==>
    ?rtv. evaluate_type tenv result_ty = SOME rtv /\
          ALOOKUP ftypes field_id = SOME rtv
Proof
  rpt strip_tac >>
  qpat_x_assum `attribute_type_ok _ _ _ _` mp_tac >>
  simp[attribute_type_ok_def, AllCaseEqs()] >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  `ALOOKUP args field_id = SOME result_ty` by
    (Cases_on `ALOOKUP args field_id` >> gvs[]) >>
  drule OPT_MMAP_ALOOKUP_ZIP >>
  disch_then drule >> strip_tac >>
  qexists_tac `tv` >> simp[] >>
  irule (cj 1 evaluate_type_mono) >> metis_tac[]
QED

(* Bridge: OPT_MMAP over MAP (expr_type o SND) kes + LIST_REL over MAP SND kes
   => LIST_REL value_has_type tvs x *)
Theorem OPT_MMAP_LIST_REL_bridge[local]:
  !kes x tvs tenv.
    OPT_MMAP (evaluate_type tenv) (MAP (expr_type o SND) kes) = SOME tvs /\
    LIST_REL (\v e. ?tyv. evaluate_type tenv (expr_type e) = SOME tyv /\
                          value_has_type tyv v) x (MAP SND kes) ==>
    LIST_REL value_has_type tvs x
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >> simp[OPT_MMAP_def, AllCaseEqs()] >> strip_tac >>
  gvs[LIST_REL_CONS2] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem struct_value_well_typed[local]:
  !tenv id args kes x.
    FLOOKUP tenv (string_to_num id) = SOME (StructArgs args) /\
    well_formed_type tenv (StructT id) /\
    MAP FST kes = MAP FST args /\
    MAP (expr_type o SND) kes = MAP SND args /\
    LIST_REL (\v e. ?tyv. evaluate_type tenv (expr_type e) = SOME tyv /\
                          value_has_type tyv v) x (MAP SND kes) ==>
    ?tyv. evaluate_type tenv (StructT id) = SOME tyv /\
          value_has_type tyv (StructV (ZIP (MAP FST args, x)))
Proof
  rpt strip_tac >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  drule evaluate_type_StructT_is_StructTV >> strip_tac >> gvs[] >>
  simp[value_has_type_def] >>
  qpat_x_assum `evaluate_type _ (StructT _) = _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >>
  drule OPT_MMAP_evaluate_type_mono >> strip_tac >>
  qpat_x_assum `ZIP _ = ftypes` (SUBST_ALL_TAC o SYM) >>
  (* Goal: struct_has_type (ZIP (MAP FST args, tvs)) (ZIP (MAP FST args, x)) *)
  (* Forward: substitute MAP SND args in OPT_MMAP, then apply bridge *)
  qpat_x_assum `MAP (expr_type o SND) kes = MAP SND args`
    (fn eq =>
      qpat_x_assum `OPT_MMAP (evaluate_type tenv) (MAP SND args) = _`
        (fn th => ASSUME_TAC (PURE_ONCE_REWRITE_RULE [GSYM eq] th) >>
                  ASSUME_TAC eq)) >>
  drule_all OPT_MMAP_LIST_REL_bridge >> strip_tac >>
  irule struct_has_type_zip_same_names >>
  imp_res_tac LIST_REL_LENGTH >> imp_res_tac OPT_MMAP_LENGTH >>
  gvs[LENGTH_MAP]
QED

Resume eval_preserves_swt[StructLit]:
  tp_p7_prefix_tac wte_StructLit ev_StructLit >>
  (* eval: vs <- eval_exprs cx (MAP SND kes); return (Value (StructV ...)) *)
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Apply P8 IH — guarded by ks = MAP FST kes (trivially true) *)
  first_x_assum (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac std_ss [] >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  ASM_REWRITE_TAC [] >>
  (* materialise (Value (StructV ...)) is trivial *)
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[materialise_Value, expr_type_def, toplevel_value_typed_def] >>
  drule_all struct_value_well_typed >> simp[]
QED

Resume eval_preserves_swt[Subscript]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_Subscript]) >>
  imp_res_tac env_consistent_type_defs >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Subscript] >>
  simp_tac std_ss [bind_apply, BETA_THM, LET_THM, ignore_bind_apply] >>
  (* Step 1: eval_expr cx e st *)
  Cases_on `eval_expr cx e st` >> rename1 `(res_e, st_e)` >>
  reverse (Cases_on `res_e`) >> simp_tac (srw_ss()) []
  >- (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!env st res st'. well_typed_expr _ e /\ _ ==> _`
        drule_all >> strip_tac >> ASM_REWRITE_TAC[] >> not_return_tac) >>
  (* e succeeded: apply unguarded IH for e *)
  qpat_x_assum `!env st res st'. well_typed_expr _ e /\ _ ==> _`
    drule_all >> strip_tac >>
  (* Discharge guarded IH for e': specialize guard with (st, x, st_e) *)
  qpat_x_assum `!s'' tv1 t. eval_expr _ e _ = _ ==> _`
    (fn ih => mp_tac (ih |> Q.SPECL [`st`, `x`, `st_e`])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* Step 2: eval_expr cx e' st_e *)
  Cases_on `eval_expr cx e' st_e` >> rename1 `(res_e', st_e')` >>
  reverse (Cases_on `res_e'`) >> simp_tac (srw_ss()) []
  >- (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> strip_tac >>
      ASM_REWRITE_TAC[] >> not_return_tac) >>
  (* e' succeeded: apply guarded IH for e' *)
  first_x_assum drule_all >> strip_tac >>
  (* All IHs discharged. Suspend the remaining pure chain. *)
  suspend "Subscript_tail"
QED

Resume eval_preserves_swt[Subscript_tail]:
  strip_tac >>
  (* Case split on the toplevel_value x' (from eval_expr e') *)
  Cases_on `x'` >>
  gvs[get_Value_def, lift_option_type_def, bind_apply,
      return_def, raise_def, lift_sum_def] >>
  TRY (tp_err_tac >> NO_TAC) >>
  (* x' = Value v — now split on evaluate_type *)
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)` >>
  gvs[lift_option_type_def, return_def, raise_def, bind_apply] >>
  TRY (tp_err_tac >> NO_TAC) >>
  rename1 `evaluate_type _ _ = SOME arr_tv` >>
  (* Split on check_array_bounds result *)
  Cases_on `check_array_bounds cx x v st_e'` >> rename1 `(cab_r, cab_s)` >>
  imp_res_tac check_array_bounds_state >> rpt BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `cab_r`) >>
  gvs[raise_def, return_def, bind_apply, lift_sum_def] >>
  TRY (tp_err_tac >> NO_TAC) >>
  (* Split on evaluate_subscript *)
  Cases_on `evaluate_subscript (get_tenv cx) arr_tv x v` >>
  gvs[raise_def, return_def] >> TRY (tp_err_tac >> NO_TAC) >>
  (* Split value vs storage ref *)
  suspend "Subscript_result"
QED

Resume eval_preserves_swt[Subscript_result]:
  imp_res_tac subscript_type_ok_not_NoneTV >>
  imp_res_tac toplevel_value_typed_not_HashMapRef >>
  drule_all evaluate_subscript_typed >> strip_tac >>
  Cases_on `x'` >> gvs[]
  >- suspend "Subscript_INL"
  >> suspend "Subscript_INR"
QED

Resume eval_preserves_swt[Subscript_INL]:
  gvs[return_def] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC
  >- (qexists_tac `rtv` >> gvs[expr_type_def])
  >> imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[] >>
  qexists_tac `rtv` >> gvs[expr_type_def] >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] toplevel_value_typed_materialise) >>
  first_assum (irule_at Any) >>
  first_assum (irule_at Any) >>
  irule evaluate_subscript_toplevel_wf >>
  first_assum (irule_at Any) >>
  imp_res_tac (cj 8 eval_expr_toplevel_wf) >>
  gvs[]
QED

Resume eval_preserves_swt[Subscript_INR]:
  PairCases_on `y` >> gvs[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  Cases_on `read_storage_slot cx y0 y1 rtv cab_s` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [raise_def, return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_storage_slot_state >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qexists_tac `rtv` >> gvs[expr_type_def, toplevel_value_typed_def] >>
  imp_res_tac read_storage_slot_well_typed >>
  imp_res_tac (cj 1 evaluate_type_well_formed) >> gvs[]
QED

Resume eval_preserves_swt[Attribute]:
  tp_p7_prefix_tac wte_Attribute ev_Attribute >>
  (* Step 1: eval_expr cx e *)
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  (* Step 2: get_Value *)
  Cases_on `get_Value x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  imp_res_tac get_Value_state >> rpt BasicProvers.VAR_EQ_TAC >>
  (* Step 3: lift_sum (evaluate_attribute) *)
  Cases_on `evaluate_attribute x' id` >> simp_tac (srw_ss()) [lift_sum_def] >>
  TRY (simp_tac (srw_ss()) [raise_def] >>
       tp_bind_err_tac >> not_return_tac >> NO_TAC) >>
  simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  (* State: st' = r (state after eval_expr, everything else pure) *)
  (* P7 IH gives swt+ec for r *)
  first_x_assum drule_all >> strip_tac >>
  ASM_REWRITE_TAC [] >>
  (* materialise (Value v) is trivial *)
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[materialise_Value, expr_type_def, toplevel_value_typed_def] >>
  (* get_Value → materialise bridge, then apply materialise IH *)
  tp_materialise_bridge_tac >>
  (* attribute_type_ok says expr_type e must be StructT *)
  `?sname. expr_type e = StructT sname` by
    (qpat_x_assum `attribute_type_ok _ _ _ _` mp_tac >>
     Cases_on `expr_type e` >> simp_tac (srw_ss()) [attribute_type_ok_def]) >>
  (* Rewrite evaluate_type to StructT, then decompose to get StructTV *)
  qpat_x_assum `evaluate_type _ (expr_type _) = _` mp_tac >>
  qpat_x_assum `attribute_type_ok _ (expr_type _) _ _` mp_tac >>
  ASM_REWRITE_TAC [] >> rpt strip_tac >>
  (* evaluate_type (StructT sname) = SOME tyv ==> tyv = StructTV ftypes *)
  qpat_assum `evaluate_type _ (StructT _) = SOME _`
    (strip_assume_tac o MATCH_MP evaluate_type_StructT_is_StructTV) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Now use attribute_type_ok_evaluate — evaluate_type assumption still available *)
  drule attribute_type_ok_evaluate >>
  disch_then drule >> strip_tac >>
  qexists_tac `rtv` >> ASM_REWRITE_TAC [] >>
  (* evaluate_attribute_well_typed closes value_has_type *)
  drule evaluate_attribute_well_typed >>
  disch_then (fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >>
  qpat_x_assum `ALOOKUP _ _ = SOME rtv`
    (fn th1 => qpat_x_assum `ALOOKUP _ _ = SOME tv`
      (fn th2 => ASSUME_TAC (TRANS (SYM th1) th2))) >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  rpt BasicProvers.VAR_EQ_TAC >> ASM_REWRITE_TAC []
QED

val toplevel_array_length_pure = TAC_PROOF(([],
  ``!cx tv st r st'. toplevel_array_length cx tv st = (r, st') ==> st' = st``),
  Cases_on `tv`
  THEN TRY (rename1 `ArrayRef itr bs _ d` THEN Cases_on `d`)
  THEN TRY (rename1 `Value v` THEN Cases_on `v`
    THEN TRY (rename1 `ArrayV av` THEN Cases_on `av`))
  THEN simp[toplevel_array_length_def, return_def, raise_def, bind_apply,
     get_storage_backend_def, get_transient_storage_def, get_accounts_def]
  THEN Cases_on `itr`
  THEN simp[get_storage_backend_def, bind_apply,
     get_transient_storage_def, get_accounts_def, return_def]
);

Resume eval_preserves_swt[Builtin]:
  rpt gen_tac >> DISCH_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_Builtin]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [ev_Builtin, type_check_def, assert_def,
    bind_apply, BETA_THM, return_def, raise_def, COND_RATOR] >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH es)`) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  simp_tac (srw_ss()) [assert_def, raise_def, return_def,
       bind_apply, ignore_bind_apply] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> simp_tac (srw_ss()) [] >> NO_TAC) >>
  Cases_on `bt = Len`
  >- (pop_assum SUBST_ALL_TAC >> suspend "Builtin_Len")
  >> suspend "Builtin_NonLen"
QED

val mult_bound_lemma = prove(
  ``!a b c. a * b < c /\ 0 < b ==> a < c``,
  rpt strip_tac >> spose_not_then assume_tac >>
  `c <= a` by decide_tac >>
  `c * b <= a * b` by simp[] >>
  `c * 1 <= c * b` by simp[] >>
  decide_tac);

val dyn_array_bound_lemma = prove(
  ``!len n tss c. len <= n /\ 0 < tss /\ 1 + n * tss < c ==> len < c``,
  rpt strip_tac >>
  `n * tss < c` by decide_tac >>
  `n < c` by (irule mult_bound_lemma >> qexists `tss` >> simp[]) >>
  decide_tac);

val fold_dimword_256 = GSYM (wordsLib.SIZES_CONV ``dimword (:256)``);

val intv_uint256_well_typed = prove(
  ``!len. len < dimword(:256) ==>
    value_has_type (BaseTV (UintT 256)) (IntV (&len))``,
  rw[value_has_type_def, integerTheory.NUM_OF_INT,
     integerTheory.INT_LE, wordsTheory.dimword_def]);

(* Helper: evaluate_type for ArrayT extracts bounds without triggering SIZES_CONV *)
val evaluate_type_ArrayT_inv = prove(
  ``!tenv t bd atv.
    evaluate_type tenv (ArrayT t bd) = SOME atv ==>
    ?tv. atv = ArrayTV tv bd /\ evaluate_type tenv t = SOME tv /\
         0 < type_slot_size tv /\ type_slot_size atv < dimword(:256)``,
  rpt strip_tac >>
  qpat_x_assum `_ = SOME _` mp_tac >>
  simp_tac bool_ss [evaluate_type_def, AllCaseEqs(), LET_THM] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qexists `tv` >> fs[]);

(* Helper: evaluate_type for BaseT always gives BaseTV *)
val evaluate_type_BaseT_inv = prove(
  ``!tenv bt tv.
    evaluate_type tenv (BaseT bt) = SOME tv ==> tv = BaseTV bt``,
  rpt strip_tac >>
  qpat_x_assum `_ = SOME _` mp_tac >>
  simp[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  strip_tac >> fs[]);

Theorem toplevel_array_length_len_bounded:
  !cx tv st len st'.
    toplevel_array_length cx tv st = (INL len, st') ==>
    !tyv. toplevel_value_typed tv tyv ==>
    !tenv typ. evaluate_type tenv typ = SOME tyv ==> is_sized_type typ ==>
    len < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> rpt strip_tac >>
  Cases_on `typ` >>
  full_simp_tac bool_ss [is_sized_type_def] >>
  Cases_on `tv`
  (* === BaseT cases === *)
  >~ [`Value v`, `BaseT b`]
  >- suspend "BaseT_Value"
  >~ [`ArrayRef`, `BaseT b`]
  >- suspend "BaseT_ArrayRef"
  >~ [`HashMapRef`, `BaseT b`]
  >- suspend "BaseT_HashMapRef"
  (* === ArrayT cases === *)
  >~ [`Value v`, `ArrayT`]
  >- suspend "ArrayT_Value"
  >~ [`HashMapRef`, `ArrayT`]
  >- suspend "ArrayT_HashMapRef"
  >~ [`ArrayRef`, `ArrayT`]
  >- suspend "ArrayT_ArrayRef"
QED

Resume toplevel_array_length_len_bounded[BaseT_Value]:
  (* BaseT / Value: is_sized_type (BaseT b) means b = StringT or BytesT *)
  drule evaluate_type_BaseT_inv >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  full_simp_tac bool_ss [toplevel_value_typed_def] >>
  Cases_on `b` >> full_simp_tac bool_ss [is_sized_type_def]
  >- ((* StringT n *)
    rename1 `StringT n` >>
    Cases_on `v` >> full_simp_tac (srw_ss()) [value_has_type_def] >>
    full_simp_tac (srw_ss()) [toplevel_array_length_def,
      return_def, raise_def, bind_apply] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    PURE_REWRITE_TAC[fold_dimword_256] >>
    fs[evaluate_type_def, LET_THM] >>
    rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
    rpt BasicProvers.VAR_EQ_TAC >> decide_tac)
  >- ((* BytesT *)
    rename1 `BytesT bsz` >> Cases_on `bsz` >>
    full_simp_tac bool_ss [is_sized_type_def]
    >- ((* Fixed n *)
      rename1 `Fixed n` >>
      Cases_on `v` >> full_simp_tac (srw_ss()) [value_has_type_def] >>
      full_simp_tac (srw_ss()) [toplevel_array_length_def,
        return_def, raise_def, bind_apply] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[evaluate_type_def, LET_THM] >>
      rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
      rpt BasicProvers.VAR_EQ_TAC >> decide_tac)
    >- ((* Dynamic n *)
      rename1 `Dynamic n` >>
      Cases_on `v` >> full_simp_tac (srw_ss()) [value_has_type_def] >>
      full_simp_tac (srw_ss()) [toplevel_array_length_def,
        return_def, raise_def, bind_apply] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      PURE_REWRITE_TAC[fold_dimword_256] >>
      fs[evaluate_type_def, LET_THM] >>
      rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
      rpt BasicProvers.VAR_EQ_TAC >> decide_tac))
QED

Resume toplevel_array_length_len_bounded[BaseT_ArrayRef]:
  (* BaseT / ArrayRef — contradiction: BaseTV b ≠ ArrayTV *)
  drule evaluate_type_BaseT_inv >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[toplevel_value_typed_def]
QED

Resume toplevel_array_length_len_bounded[BaseT_HashMapRef]:
  (* BaseT / HashMapRef — contradiction: BaseTV b ≠ NoneTV *)
  drule evaluate_type_BaseT_inv >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[toplevel_value_typed_def]
QED

Resume toplevel_array_length_len_bounded[ArrayT_Value]:
  (* ArrayT / Value *)
  drule evaluate_type_ArrayT_inv >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `toplevel_value_typed _ _` mp_tac >>
  rewrite_tac[toplevel_value_typed_def] >> strip_tac >>
  Cases_on `v` >> full_simp_tac bool_ss [value_has_type_def] >>
  Cases_on `a` >> full_simp_tac bool_ss [value_has_type_def] >>
  Cases_on `b` >> full_simp_tac bool_ss [value_has_type_def,
    toplevel_array_length_def, return_def, raise_def, bind_apply,
    sumTheory.sum_distinct, sumTheory.INL_11, PAIR_EQ] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `type_slot_size _ < _` mp_tac >>
  rewrite_tac[type_slot_size_def] >> strip_tac >>
  irule dyn_array_bound_lemma >>
  qexistsl [`n`, `type_slot_size tv`] >>
  full_simp_tac bool_ss []
QED

Resume toplevel_array_length_len_bounded[ArrayT_HashMapRef]:
  (* ArrayT / HashMapRef — contradiction: ArrayTV ≠ NoneTV *)
  drule evaluate_type_ArrayT_inv >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[toplevel_value_typed_def]
QED

Resume toplevel_array_length_len_bounded[ArrayT_ArrayRef]:
  (* ArrayT / ArrayRef: toplevel_value_typed gives ArrayTV tv bd = ArrayTV tv' bd' *)
  drule evaluate_type_ArrayT_inv >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `toplevel_value_typed _ _` mp_tac >>
  rewrite_tac[toplevel_value_typed_def] >> strip_tac >>
  (* Resolve ArrayTV tv bd = ArrayTV t' b0 *)
  gvs[] >>
  Cases_on `b`
  >- suspend "ArrayRef_Fixed"
  >- suspend "ArrayRef_Dynamic"
QED

Resume toplevel_array_length_len_bounded[ArrayRef_Fixed]:
  full_simp_tac bool_ss
    [toplevel_array_length_def, return_def, raise_def, bind_apply,
     sumTheory.INL_11, PAIR_EQ] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* type_slot_size bound is in assumptions; fold numeral, extract *)
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [fold_dimword_256]) >>
  qpat_x_assum `type_slot_size _ < _` mp_tac >>
  rewrite_tac[type_slot_size_def] >> strip_tac >>
  PURE_REWRITE_TAC[fold_dimword_256] >>
  irule mult_bound_lemma >> qexists `type_slot_size t'` >>
  full_simp_tac bool_ss []
QED

Resume toplevel_array_length_len_bounded[ArrayRef_Dynamic]:
  qpat_x_assum `toplevel_array_length _ _ _ = _` mp_tac >>
  Cases_on `b'` >>
  simp[toplevel_array_length_def, bind_apply,
       get_storage_backend_def, get_transient_storage_def,
       get_accounts_def, return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  PURE_REWRITE_TAC[fold_dimword_256] >>
  simp[wordsTheory.w2n_lt]
QED

Finalise toplevel_array_length_len_bounded;

val wte_singleton_hd = prove(
  ``well_typed_exprs env es /\ LENGTH es = 1 ==> well_typed_expr env (HD es)``,
  Cases_on `es` >> simp[wte_exprs_cons]);

Resume eval_preserves_swt[Builtin_Len]:
  markerLib.RESUME_TAC >>
  (* Extract and simplify P7 IH (CONJUNCT2), discharge type_check guard *)
  qpat_x_assum `_ /\ _` (fn ihs =>
    ASSUME_TAC (SIMP_RULE (srw_ss())
      [type_check_def, assert_def, return_def,
       builtin_args_length_ok_def, bind_apply] (CONJUNCT2 ihs))) >>
  (* Extract well_typed_builtin_app facts *)
  qpat_x_assum `well_typed_builtin_app _ Len _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_builtin_app_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Simplify Len = Len in goal, unfold monadic chain *)
  simp_tac (srw_ss()) [bind_apply, return_def] >>
  strip_tac >>
  (* well_typed_expr for HD es: from well_typed_exprs, LENGTH = 1 *)
  (* Derive well_typed_expr for HD es before suspending *)
  drule_all wte_singleton_hd >> strip_tac >>
  (* Discharge IH guard: LENGTH es = 1 ==> ... becomes ... *)
  qpat_x_assum `LENGTH es = 1 ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "Builtin_Len_main"
QED

Resume eval_preserves_swt[Builtin_Len_main]:
  Cases_on `eval_expr cx (HD es) st` >>
  rename1 `eval_expr cx (HD es) st = (res_e, st_e)` >>
  first_x_assum (qspecl_then [`env`, `st`, `res_e`, `st_e`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  reverse (Cases_on `res_e`)
  >- ((* INR: eval_expr failed *)
    ASM_REWRITE_TAC [] >>
    simp_tac (srw_ss()) [] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> gvs[])
  >>
  (* INL: eval_expr succeeded *)
  rename1 `eval_expr _ _ _ = (INL tv_e, st_e)` >>
  ASM_REWRITE_TAC [] >> simp_tac (srw_ss()) [bind_apply] >>
  Cases_on `toplevel_array_length cx tv_e st_e` >>
  rename1 `toplevel_array_length cx tv_e st_e = (res_len, st_len)` >>
  `st_len = st_e` by metis_tac[toplevel_array_length_pure] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `res_len`)
  >- ((* INR: toplevel_array_length failed *)
    ASM_REWRITE_TAC [] >>
    simp_tac (srw_ss()) [] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> gvs[])
  >>
  (* INL: toplevel_array_length succeeded *)
  rename1 `toplevel_array_length _ _ _ = (INL len_n, _)` >>
  ASM_REWRITE_TAC [] >> simp_tac (srw_ss()) [return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `?tyv_e. evaluate_type (get_tenv cx) (expr_type (HD es)) = SOME tyv_e /\
           toplevel_value_typed tv_e tyv_e` by
    (first_x_assum (qspec_then `tv_e` mp_tac) >> simp[]) >>
  `is_sized_type (expr_type (HD es))` by
    (Cases_on `es` >> gvs[]) >>
  `len_n < dimword(:256)` by
    metis_tac[toplevel_array_length_len_bounded] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >> rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[toplevel_value_typed_def, materialise_Value, return_def] >>
  qexists `BaseTV (UintT 256)` >>
  simp[expr_type_def, evaluate_type_def, LET_THM] >>
  PURE_REWRITE_TAC[fold_dimword_256] >>
  irule intv_uint256_well_typed >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [fold_dimword_256]) >>
  first_assum ACCEPT_TAC
QED

val map_eq_implies_length = prove(
  ``!f xs ys. MAP f xs = ys ==> LENGTH xs = LENGTH ys``,
  rw[] >> simp[LENGTH_MAP]);
val wtba_implies_balok = prove(
  ``!ty bt es. well_typed_builtin_app ty bt (MAP expr_type es) ==>
        builtin_args_length_ok bt (LENGTH es)``,
  rpt strip_tac >> Cases_on `bt` >>
  fs[well_typed_builtin_app_def, builtin_args_length_ok_def,
     compatible_bound_def] >>
  imp_res_tac map_eq_implies_length >> fs[]);

Resume eval_preserves_swt[Builtin_NonLen]:
  markerLib.RESUME_TAC >>
  (* Simplify if-then-else: bt <> Len is in assumptions *)
  ASM_REWRITE_TAC [] >>
  simp_tac (srw_ss()) [bind_apply, BETA_THM] >>
  (* Extract and simplify P8 IH (CONJUNCT1), discharge type_check guard *)
  qpat_x_assum `_ /\ _` (fn ihs =>
    ASSUME_TAC (SIMP_RULE (srw_ss())
      [type_check_def, assert_def, return_def] (CONJUNCT1 ihs))) >>
  (* Derive builtin_args_length_ok from well_typed_builtin_app *)
  `builtin_args_length_ok bt (LENGTH es)` by
    (imp_res_tac wtba_implies_balok) >>
  (* Step 1: eval_exprs cx es st *)
  Cases_on `eval_exprs cx es st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) []
  >- (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> tp_bind_err_tac) >>
  rename1 `eval_exprs cx es st = (INL vs_e, st_e)` >>
  (* Apply P8 IH *)
  first_x_assum drule_all >> strip_tac >>
  (* Step 2: get_accounts (pure — always returns INL) *)
  simp_tac (srw_ss()) [get_accounts_def, return_def, bind_apply, BETA_THM] >>
  (* Step 3: Cases on evaluate_builtin result — pure sum *)
  reverse (Cases_on `evaluate_builtin cx st_e.accounts ty bt vs_e`) >>
  simp_tac (srw_ss()) [lift_sum_def, return_def, raise_def]
  >- ( (* evaluate_builtin failed: INR e *)
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> gvs[]) >>
  (* evaluate_builtin succeeded: INL v — suspend for clean proof *)
  suspend "Builtin_INL"
QED

Resume eval_preserves_swt[Builtin_INL]:
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  gvs[materialise_def, return_def] >>
  simp_tac (srw_ss()) [expr_type_def, toplevel_value_typed_def] >>
  imp_res_tac env_consistent_type_defs >>
  (* Use evaluate_builtin_well_typed - supply arg_tys witness *)
  `evaluate_builtin cx st'.accounts ty bt vs_e = INL x /\
   well_typed_builtin_app ty bt (MAP expr_type es) /\
   context_well_typed cx /\
   LIST_REL (\v t. ?tyv. evaluate_type (get_tenv cx) t = SOME tyv /\
                          value_has_type tyv v) vs_e (MAP expr_type es) /\
   IS_SOME (evaluate_type (get_tenv cx) ty)` by (
    rpt CONJ_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- (REWRITE_TAC [LIST_REL_MAP2] >> BETA_TAC >> first_assum ACCEPT_TAC)
    >- gvs[well_formed_type_def]) >>
  metis_tac[evaluate_builtin_well_typed]
QED

Resume eval_preserves_swt[Pop]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Decompose well_typed_expr for Pop *)
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_Pop]) >>
  (* Wrap well_typed_target for P5 IH *)
  qpat_assum `well_typed_target env bt _`
    (fn th => ASSUME_TAC (Q.EXISTS (`?ty. well_typed_target env bt ty`,
                                    `ArrayT v11 bd`) th)) >>
  (* Unfold ev_Pop *)
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Pop] >>
  simp_tac std_ss [bind_apply, BETA_THM, UNCURRY] >>
  (* Step 1: eval_base_target cx bt st *)
  Cases_on `eval_base_target cx bt st` >> rename1 `(res_bt, st_bt)` >>
  reverse (Cases_on `res_bt`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  Cases_on `x` >> simp_tac (srw_ss()) [] >>
  rename1 `eval_base_target cx bt st = (INL (loc, sbs), st_bt)` >>
  (* P5 IH *)
  first_x_assum drule_all >> strip_tac >>
  (* Step 2: assign_target cx (BaseTargetV loc sbs) PopOp st_bt *)
  Cases_on `assign_target cx (BaseTargetV loc sbs) PopOp st_bt` >>
  rename1 `assign_target _ _ _ st_bt = (res_at, st_at)` >>
  (* State preservation via assign_target_well_typed_ao *)
  `state_well_typed st_at /\ env_consistent env cx st_at` by (
    irule assign_target_well_typed_ao >>
    rpt (first_assum (irule_at Any)) >>
    rpt strip_tac >>
    irule assign_subscripts_preserves_type >>
    rpt (first_assum (irule_at Any)) >>
    rpt CONJ_TAC >> TRY (rpt strip_tac >> gvs[] >> NO_TAC) >>
    rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac (srw_ss()) [pop_element_def, AllCaseEqs()]
  ) >>
  reverse (Cases_on `res_at`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> gvs[] >>
       imp_res_tac (cj 1 assign_target_no_return) >>
       first_x_assum (qspec_then `v` mp_tac) >>
       simp_tac (srw_ss()) [] >> NO_TAC) >>
  (* Step 3: lift_option_type popped "Pop returned NONE" *)
  Cases_on `x` >> simp_tac (srw_ss()) [lift_option_type_def, return_def, raise_def] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  (* Step 4: return (Value x') — the main value *)
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  (* Value typing: materialise (Value x') = (INL x', st') *)
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[materialise_def, return_def, expr_type_def, toplevel_value_typed_def] >>
  suspend "Pop_vht"
QED

Resume eval_preserves_swt[Pop_vht]:
  (* Goal: ∃tyv. evaluate_type v11 = SOME tyv ∧ value_has_type tyv v
     where assign_target cx (BaseTargetV loc sbs) PopOp st_bt = (INL (SOME v), st')
     and well_typed_target env bt (ArrayT v11 bd) *)
  irule assign_target_pop_value_well_typed >>
  metis_tac[]
QED

Resume eval_preserves_swt[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_TypeBuiltin]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_TypeBuiltin] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, BETA_THM] >>
  simp_tac (srw_ss()) [type_check_def, assert_def] >>
  reverse (Cases_on `type_builtin_args_length_ok tb (LENGTH es)`) >>
  ASM_REWRITE_TAC[] >> simp_tac (srw_ss()) [raise_def] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       ASM_REWRITE_TAC[] >> NO_TAC) >>
  (* Discharge guarded P8 IH: intro and simplify guard *)
  last_x_assum mp_tac >>
  disch_then (mp_tac o Q.SPECL [`st`, `()`, `st`]) >>
  simp_tac (srw_ss()) [type_check_def, assert_def] >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  disch_then assume_tac >>
  (* Intro the main eval chain *)
  strip_tac >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs _ _ _ = (res_es, st1)` >>
  (* Use P8 IH *)
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  reverse (Cases_on `res_es`) >> simp_tac (srw_ss()) [] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       ASM_REWRITE_TAC[sumTheory.INR_neq_INL] >> NO_TAC) >>
  (* eval_exprs success: peel lift_sum *)
  simp_tac std_ss [lift_sum_def, bind_apply, BETA_THM] >>
  Cases_on `evaluate_type_builtin cx tb typ x` >>
  simp_tac (srw_ss()) [return_def, raise_def] >>
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
       ASM_REWRITE_TAC[sumTheory.INR_neq_INL] >> NO_TAC) >>
  (* evaluate_type_builtin success *)
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  ASM_REWRITE_TAC[] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[materialise_def, return_def, expr_type_def, toplevel_value_typed_def] >>
  `env.type_defs = get_tenv cx` by gvs[env_consistent_def] >>
  `IS_SOME (evaluate_type (get_tenv cx) typ)` by
    gvs[GSYM well_formed_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[] >>
  irule evaluate_type_builtin_well_typed >>
  rpt (first_assum (irule_at Any)) >> gvs[]
QED

Resume eval_preserves_swt[Send]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_Send]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Send] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, BETA_THM] >>
  ASM_REWRITE_TAC[] >>
  simp_tac (srw_ss()) [type_check_def, assert_def] >>
  Cases_on `eval_exprs cx es st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  (* Apply guarded P8 IH for both branches *)
  first_x_assum (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  simp_tac (srw_ss()) [type_check_def, assert_def] >>
  disch_then drule_all >> strip_tac >>
  (* Error branch: IH gave swt+ec, chain returns error, done *)
  TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >> NO_TAC) >>
  (* Success branch: peel remaining chain *)
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `st'.scopes = r.scopes /\ st'.immutables = r.immutables` by
    chain_scopes_imm_tac () >>
  `state_well_typed st' /\ env_consistent env cx st'` by (
    irule tp_preserved_scopes_immutables >>
    qexists_tac `r` >> gvs[]) >>
  simp[] >>
  rpt strip_tac >>
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  qpat_x_assum `(case _ of (INL _, _) => _ | _ => _) = _` mp_tac >>
  simp_tac (srw_ss())
    [lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[materialise_def, return_def, expr_type_def, toplevel_value_typed_def,
      evaluate_type_def, value_has_type_def]
QED

(* Uncurry ONLY the outer guard of an IH (not inner body conjunctions).
   ∀vars. (C1 ∧ ... ∧ Cn) ==> ∀xs. body_conj ==> concl
   becomes: ∀vars. C1 ==> ... ==> Cn ==> ∀xs. body_conj ==> concl *)
fun UNCURRY_GUARD_CONV tm =
  (REWR_CONV (GSYM AND_IMP_INTRO) THENC
   RAND_CONV (TRY_CONV UNCURRY_GUARD_CONV)) tm;

(* Uncurry guard and drule-chain n guard conjuncts against assumptions.
   Leaves IH body (with conjunctive antecedent) as implication on goal. *)
fun uncurry_drule_chain n ih_thm =
  let val ih_uc = CONV_RULE (STRIP_QUANT_CONV UNCURRY_GUARD_CONV) ih_thm
  in drule ih_uc >> NTAC (n - 1) (disch_then drule) end;

val ih_mdefs = [bind_apply, pair_bind_apply, check_def, assert_def,
  return_def, raise_def, lift_option_type_def, lift_option_def,
  ignore_bind_apply, get_accounts_def, get_transient_storage_def,
  update_accounts_def, update_transient_def, lift_sum_runtime_def,
  case_lift_option];

Resume eval_preserves_swt[ExtCall]:
  (* IHs in SML bindings. P7 IH pre-simplified with SIMP_RULE std_ss []
     to substitute equalities (tenv, txParams, caller, result destructuring,
     returnData=[]), then drule_all matches remaining guard conjuncts. *)
  rpt gen_tac >> disch_then STRIP_ASSUME_TAC >>
  pop_assum $ markerLib.ASSUME_NAMED_TAC "ih_p8" >>
  pop_assum $ markerLib.ASSUME_NAMED_TAC "ih_p7" o
                SIMP_RULE std_ss [] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_ExtCall]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_ExtCall] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply] >>
  (* 1. eval_exprs cx es *)
  BasicProvers.TOP_CASE_TAC >>
  markerLib.LABEL_X_ASSUM "ih_p8" assume_tac >>
  first_x_assum drule_all >> strip_tac >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 2. check (vs <> []) *)
  BasicProvers.TOP_CASE_TAC >> imp_res_tac check_state >>
  BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 3. lift_option_type (dest_AddressV ...) *)
  BasicProvers.TOP_CASE_TAC >> imp_res_tac lift_option_type_state >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  BasicProvers.VAR_EQ_TAC >>
  (* 4. if-then-else (is_static branch) — doesn't change state *)
  simp[bind_def] >>
  BasicProvers.TOP_CASE_TAC >>
  (fn (asl, g) =>
    let val asm = hd asl
        val (lhs, rhs) = dest_eq asm
        val (_, out_st) = pairSyntax.dest_pair rhs
        val in_st = rand lhs
    in
      (SUBGOAL_THEN (mk_eq(out_st, in_st)) SUBST_ALL_TAC >- (
        gvs[COND_RATOR, AllCaseEqs(), return_def, ignore_bind_apply,
            bind_apply] >>
        imp_res_tac check_state >>
        imp_res_tac lift_option_type_state >>
        rw[] >> gvs[] )) (asl, g)
    end) >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 5. pairarg for (value_opt, arg_vals) *)
  pairarg_tac >> BasicProvers.VAR_EQ_TAC >>
  simp_tac std_ss [] >>
  simp_tac (srw_ss()) [bind_apply] >>
  (* 6. lift_option build_ext_calldata *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 7-8. get_accounts, get_transient_storage *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac get_accounts_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  rewrite_tac[ignore_bind_apply, bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac get_transient_storage_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  rewrite_tac[bind_apply] >>
  (* 9. lift_option (run_ext_call ...) *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 10. pairarg for (success,returnData,accounts',tStorage') *)
  pairarg_tac >> BasicProvers.VAR_EQ_TAC >>
  simp_tac std_ss [] >>
  simp_tac (srw_ss()) [bind_apply, ignore_bind_apply] >>
  (* 11. check success *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 12. update_accounts (K accounts') *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac update_accounts_scopes >>
  imp_res_tac update_accounts_immutables >>
  BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- gvs[update_accounts_def, return_def] >>
  (* 13. update_transient (K tStorage') *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac update_transient_scopes >>
  imp_res_tac update_transient_immutables >>
  reverse BasicProvers.TOP_CASE_TAC >- gvs[update_transient_def, return_def] >>
  (* Tail: if returnData = [] /\ IS_SOME drv *)
  reverse IF_CASES_TAC >- (
    (* Non-drv path: state preservation + value typing (no P7 IH needed) *)
    simp_tac (srw_ss()) [bind_apply, lift_sum_runtime_def] >>
    strip_tac >>
    reverse BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]
    >- (irule tp_preserved_scopes_immutables >>
        qexists_tac `r` >> simp[]) >>
    `state_well_typed r' /\ env_consistent env cx r'` by (
      irule tp_preserved_scopes_immutables >>
      qexists_tac `r` >> simp[] ) >>
    simp[expr_type_def, toplevel_value_typed_def,
         materialise_def, return_def] >>
    `env.type_defs = get_tenv cx` by
      (imp_res_tac env_consistent_type_defs >> simp[]) >>
    `?tyv. evaluate_type (get_tenv cx) ret_type = SOME tyv` by
      gvs[well_formed_type_def, IS_SOME_EXISTS] >>
    metis_tac[evaluate_abi_decode_return_well_typed]
  ) >>
  (* Drv path: substitute returnData=[] into assumptions (IH has [] inlined).
     gvs[] is safe here because IH is in SML binding, not assumptions. *)
  strip_tac >> gvs[] >>
  `state_well_typed r' /\ env_consistent env cx r'` by (
    irule tp_preserved_scopes_immutables >>
    qexists_tac `r` >> simp[] ) >>
  `well_typed_expr env (THE drv)` by (
    Cases_on `drv` >> gvs[well_typed_opt_SOME] ) >>
  `expr_type (THE drv) = ret_type` by (
    Cases_on `drv` >> gvs[] ) >>
  markerLib.LABEL_X_ASSUM "ih_p7" assume_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[expr_type_def] >> gvs[]
QED

val type_check_success = prove(
  ``type_check b s st = (INL v, st') ==> b /\ st' = st``,
  rw[type_check_def, assert_def, return_def, raise_def]);

(* IntCall: Three IHs — P1 (body stmts), P8 (defaults), P8 (args).
   Uses intcall_body_preserves_swt, intcall_cleanup_preserves_swt.
   TOP_CASE_TAC pattern from eval_preserves_tv IntCall.
   KEY: keep IHs in SML bindings, not assumptions, during chain peeling.
   This prevents TOP_CASE_TAC from finding case exprs in IH guards. *)
(* IntCall: expand pure prefix with simp_tac std_ss, use IF_CASES_TAC/Cases_on
   for splits. DON'T use TOP_CASE_TAC (leaves unresolved state variables).
   DON'T use imp_res_tac (fires on IH guard assumptions). *)
Resume eval_preserves_swt[IntCall]:
  rpt gen_tac >> disch_then STRIP_ASSUME_TAC >>
  pop_assum (fn ih_p8_args_raw =>
  pop_assum (fn ih_p8_dflts_raw =>
  pop_assum (fn ih_p1_raw =>
  let val ih_p1 = SIMP_RULE std_ss [] ih_p1_raw
      val ih_p8_dflts = SIMP_RULE std_ss [] ih_p8_dflts_raw
      val ih_p8_args = SIMP_RULE std_ss [] ih_p8_args_raw
  in
  rpt gen_tac >> strip_tac >>
  (* Establish env_consistent early, before unfolding eval_expr *)
  imp_res_tac eval_expr_preserves_ec >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_IntCall]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[ev_IntCall] >>
  simp_tac std_ss [bind_apply, ignore_bind_apply, LET_THM] >>
  (* 1. check recursion *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 2. lift_option_type get_module_code *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 3. lift_option_type lookup_callable_function *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  (* 4. type_check (LET_THM already inlined tuple LETs) *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  simp_tac std_ss [bind_apply] >>
  (* 5. eval_exprs cx es — P8 args IH *)
  BasicProvers.TOP_CASE_TAC >>
  gvs[] >>
  (fn (asl, g) => (assume_tac ih_p8_args (asl, g))) >>
  first_x_assum drule_all >> strip_tac >>
  reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
  simp_tac std_ss [bind_apply] >>
  (* 6. eval_exprs cxd needed_dflts — P8 defaults IH *)
  BasicProvers.TOP_CASE_TAC >>
  (* Step 6: discharge ih_p8_dflts guard via uncurry_drule_chain *)
  (fn (asl, g) =>
    let val ih_dflts = SIMP_RULE std_ss [] ih_p8_dflts in
    (
    (* Peel 5 guard conjuncts of ih_dflts using chain assumptions *)
    uncurry_drule_chain 5 ih_dflts >>
    (* IH body into assumptions; PairCases + FST/SND simplify *)
    disch_then assume_tac >>
    qpat_x_assum `lift_option_type (get_module_code _ _) _ _ = _`
      (strip_assume_tac o MATCH_MP lift_option_type_SOME) >>
    qpat_x_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
      (strip_assume_tac o MATCH_MP lift_option_type_SOME) >>
    PairCases_on `x''` >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [FST, SND]) >>
    pure_rewrite_tac [FST, SND] >>
    SUBGOAL_THEN ``fn_sigs_consistent env.fn_sigs cx`` assume_tac
    >- (qpat_x_assum `env_consistent env cx _` mp_tac >>
        simp_tac (srw_ss()) [env_consistent_def]) >>
    drule_all functions_well_typed_body_full >> strip_tac >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [FST, SND]) >>
    (* Re-inject ih_p1 as assumption before suspend, so it survives *)
    assume_tac ih_p1 >>
    (* Step 6b+: discharge defaults IH body, then steps 7-15 *)
    suspend "intcall_tail"
    ) (asl, g) end)
  end)))
QED

Resume eval_preserves_swt[intcall_tail]:
  (* Pop ih_p1 to keep it safe during expensive operations *)
  pop_assum (fn ih_p1 =>
  (* Step 6b: discharge defaults IH body via manual SPECL *)
  qpat_x_assum `!env st res st'. well_typed_exprs env (DROP _ _) /\ _ ==> _`
    (mp_tac o
     Q.SPECL [`<|var_types := FEMPTY; global_types := FEMPTY;
                toplevel_types := FEMPTY;
                type_defs := get_tenv (cx with stk updated_by
                               CONS (src_id_opt, fn));
                fn_sigs := FEMPTY; flag_members := FEMPTY|>`,
              `r'''`, `q`, `r'`]) >>
  impl_tac >- suspend "dflts_ih" >>
  strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [get_tenv_stk_irrelevant]) >>
  (* Re-inject ih_p1 before suspend so it survives to intcall_chain *)
  assume_tac ih_p1 >>
  suspend "intcall_chain")
QED

Resume eval_preserves_swt[dflts_ih]:
  rpt conj_tac
  >- (PURE_REWRITE_TAC [get_tenv_stk_irrelevant] >>
      irule well_typed_exprs_DROP >>
      first_assum ACCEPT_TAC)
  >- simp_tac (srw_ss()) [env_consistent_empty]
  >- first_assum ACCEPT_TAC
  >- (PURE_REWRITE_TAC [functions_well_typed_stk_irrelevant] >>
      first_assum ACCEPT_TAC)
  >- (qpat_x_assum `context_well_typed cx` mp_tac >>
      simp_tac (srw_ss()) [context_well_typed_def])
  >> first_assum ACCEPT_TAC
QED

Resume eval_preserves_swt[intcall_chain]:
  (* ih_p1 is newest assumption — pop to keep safe during gvs *)
  pop_assum (fn ih_p1 =>
  strip_tac >>
  (* INR q: error — env_consistent env cx st' already an assumption *)
  reverse (Cases_on `q`) >- gvs[] >>
  gvs[] >>
  (* Re-inject ih_p1 for later use *)
  assume_tac ih_p1 >>
  suspend "intcall_inl")
QED

(* Standalone helper: state_well_typed + value typing through
   IntCall finally + safe_cast chain. Proved separately for REPL access. *)
Theorem intcall_finally_swt_vht[local]:
  !fn_stmts saved_scopes nr is_view slot_opt target cxf
   pushed_st ret_tv env_ih ret_ty_raw res st'.
  state_well_typed pushed_st /\
  EVERY scope_well_typed saved_scopes /\
  well_typed_stmts env_ih ret_ty_raw fn_stmts /\
  env_consistent env_ih cxf pushed_st /\
  functions_well_typed cxf /\
  context_well_typed cxf /\
  evaluate_type (get_tenv cxf) ret_ty_raw = SOME ret_tv /\
  (!env_i ret_ty_i st_i res_i st_i'.
     well_typed_stmts env_i ret_ty_i fn_stmts /\
     env_consistent env_i cxf st_i /\ state_well_typed st_i /\
     functions_well_typed cxf /\ context_well_typed cxf /\
     eval_stmts cxf fn_stmts st_i = (res_i, st_i') ==>
     state_well_typed st_i' /\ env_consistent env_i cxf st_i' /\
     !v rtv. res_i = INR (ReturnException v) /\
             evaluate_type (get_tenv cxf) ret_ty_i = SOME rtv ==>
             value_has_type rtv v) /\
  (case
     finally
       (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
       (do pop_function saved_scopes;
           if nr /\ ~is_view then
             (case slot_opt of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock target slot)
           else return () od)
       pushed_st
   of
     (INL rv, s6) =>
       (case lift_option_type (safe_cast ret_tv rv)
               "IntCall cast ret" s6 of
          (INL crv, s7) => return (Value crv) s7
        | (INR e, s7) => (INR e, s7))
   | (INR e, s6) => (INR e, s6)) = (res, st') ==>
  state_well_typed st' /\
  (!crv. res = INL (Value crv) ==> value_has_type ret_tv crv) /\
  (!tv. res = INL tv ==> ?crv. tv = Value crv)
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: Name the finally result *)
  `?fres fst. finally
     (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
     (do pop_function saved_scopes;
         if nr /\ ~is_view then
           (case slot_opt of
              NONE => return ()
            | SOME slot => release_nonreentrant_lock target slot)
         else return () od)
     pushed_st = (fres, fst)` by metis_tac[pairTheory.PAIR] >>
  (* Step 2: Prove state_well_typed fst *)
  qpat_assum `finally _ _ pushed_st = _`
    (mp_tac o MATCH_MP
      (REWRITE_RULE [GSYM AND_IMP_INTRO] state_well_typed_finally)) >>
  impl_tac >- suspend "body_swt" >>
  impl_tac >- suspend "cleanup_swt" >>
  strip_tac >>
  (* Step 3: Case split on fres *)
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[] >> Cases_on `fres` >> simp[]
  >- suspend "inl_case"
  >- (strip_tac >> gvs[])
QED

Resume intcall_finally_swt_vht[body_swt]:
  rpt gen_tac >> strip_tac >>
  irule (GEN_ALL intcall_body_preserves_swt) >>
  qexistsl [`fn_stmts`, `cxf`, `pushed_st`, `r`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  (* IH: well_typed_stmts ∧ env_consistent ∧ swt ∧ fwt ∧ cwt ∧ eval_stmts = ... ⇒ swt ∧ ... *)
  last_x_assum (qspecl_then [`env_ih`, `ret_ty_raw`, `pushed_st`,
                              `res'`, `s_body`] mp_tac) >>
  simp[]
QED

Resume intcall_finally_swt_vht[cleanup_swt]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule (GEN_ALL intcall_cleanup_preserves_swt) >>
  qexistsl [`is_view`, `nr`, `saved_scopes`, `r'`, `s`, `slot_opt`, `target`] >>
  simp[]
QED

Resume intcall_finally_swt_vht[inl_case]:
  pop_assum mp_tac >>
  BasicProvers.TOP_CASE_TAC >> BasicProvers.TOP_CASE_TAC >>
  simp_tac (srw_ss()) [return_def, raise_def]
  >- ((* INL: safe_cast succeeded. rpt strip_tac splits into swt + vht + returns_value *)
      rpt strip_tac
      >- (imp_res_tac lift_option_type_state >> gvs[])
      >- (imp_res_tac lift_option_type_SOME >> suspend "vht")
      >> gvs[])
  >- ((* INR: lift_option_type returned error *)
      rpt strip_tac >> gvs[] >>
      imp_res_tac lift_option_type_state >> gvs[])
QED

Resume intcall_finally_swt_vht[vht]:
  (* Establish safe_cast ret_tv x = SOME crv *)
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac lift_option_type_SOME >>
  (* Decompose finally: x = NoneV or ReturnException *)
  first_x_assum
    (strip_assume_tac o MATCH_MP finally_try_handle_success_rv) >> gvs[]
  >- ((* NoneV case *)
      imp_res_tac safe_cast_NoneV >> gvs[value_has_type_def])
  >> (* ReturnException case: IH gives vht, safe_cast preserves *)
  irule safe_cast_preserves_well_typed >>
  first_assum (irule_at Any) >>
  last_x_assum (qspecl_then
    [`env_ih`, `ret_ty_raw`, `pushed_st`,
     `INR (ReturnException v)`, `st_bdy`] mp_tac) >>
  simp[]
QED

Finalise intcall_finally_swt_vht


(* Wraps intcall_chain_swt_vht result into the P7 goal shape.
   Handles: fn_sigs_consistent => v16=x''4, expr_type, materialise_Value,
   toplevel_value_typed. Clean statement avoids Resume block assumption issues. *)
Theorem intcall_inl_wrap[local]:
  !ret_tv fn_sigs cx src fn' ptypes v16 ts
   a b c d ty_raw fn_body env st' res.
  evaluate_type (get_tenv cx) ty_raw = SOME ret_tv /\
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src,fn') = SOME (ptypes, v16) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn' ts =
    SOME (a,b,c,d,ty_raw,fn_body) /\
  state_well_typed st' /\
  env_consistent env cx st' /\
  (!crv. res = INL (Value crv) ==> value_has_type ret_tv crv) /\
  (!tv. res = INL tv ==> ?crv. tv = Value crv) ==>
  state_well_typed st' /\
  !tv. res = INL tv ==>
    (?tyv. evaluate_type (get_tenv cx) v16 = SOME tyv /\
           toplevel_value_typed tv tyv) /\
    !v st''. materialise cx tv st' = (INL v, st'') ==>
      state_well_typed st'' /\ env_consistent env cx st'' /\
      ?tyv. evaluate_type (get_tenv cx) v16 = SOME tyv /\
            value_has_type tyv v
Proof
  rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule (iffLR fn_sigs_consistent_def |> GEN_ALL) >>
  disch_then drule >> strip_tac >>
  `v16 = ty_raw` by (`ts' = ts` by gvs[] >> gvs[]) >> gvs[] >>
  simp[toplevel_value_typed_def]
QED

Theorem intcall_chain_swt_vht[local]:
  !params args ret_ty_raw fn_stmts mut_flag nr_flag src_fn cx
   st0 ret_tv env_body res st_out.
  state_well_typed st0 /\
  functions_well_typed cx /\
  context_well_typed cx /\
  well_typed_stmts env_body ret_ty_raw fn_stmts /\
  evaluate_type (get_tenv cx) ret_ty_raw = SOME ret_tv /\
  (!env_i ret_ty_i st_i res_i st_i'.
     well_typed_stmts env_i ret_ty_i fn_stmts /\
     env_consistent env_i (cx with stk updated_by CONS src_fn) st_i /\
     state_well_typed st_i /\
     functions_well_typed (cx with stk updated_by CONS src_fn) /\
     context_well_typed (cx with stk updated_by CONS src_fn) /\
     eval_stmts (cx with stk updated_by CONS src_fn) fn_stmts st_i =
       (res_i, st_i') ==>
     state_well_typed st_i' /\
     env_consistent env_i (cx with stk updated_by CONS src_fn) st_i' /\
     !v rtv. res_i = INR (ReturnException v) /\
             evaluate_type (get_tenv (cx with stk updated_by CONS src_fn))
               ret_ty_i = SOME rtv ==>
             value_has_type rtv v) /\
  (!sc. bind_arguments (get_tenv cx) params args = SOME sc ==>
        scope_well_typed sc /\
        env_consistent env_body (cx with stk updated_by CONS src_fn)
          (st0 with scopes := [sc])) /\
  EVERY scope_well_typed st0.scopes /\
  (case lift_option_type (bind_arguments (get_tenv cx) params args)
          "IntCall bind_arguments" st0 of
     (INL env_sc, s1) =>
       (case get_scopes s1 of
          (INL prev, s2) =>
            (case lift_option_type (SOME ret_tv) "IntCall eval ret" s2 of
               (INL rtv, s3) =>
                 (case (if nr_flag then
                          case cx.nonreentrant_slot of
                            NONE => raise (Error (RuntimeError
                                      "nonreentrant slot missing"))
                          | SOME slot =>
                            acquire_nonreentrant_lock cx.txn.target slot
                              (mut_flag = View \/ mut_flag = Pure)
                        else return ()) s3 of
                    (INL lock_v, s4) =>
                      (case push_function src_fn env_sc cx s4 of
                         (INL cxf, s5) =>
                           (case finally
                              (try (do eval_stmts cxf fn_stmts;
                                       return NoneV od) handle_function)
                              (do pop_function prev;
                                  if nr_flag /\ mut_flag <> View /\
                                     mut_flag <> Pure then
                                    (case cx.nonreentrant_slot of
                                       NONE => return ()
                                     | SOME slot =>
                                       release_nonreentrant_lock
                                         cx.txn.target slot)
                                  else return () od) s5 of
                              (INL rv, s6) =>
                                (case lift_option_type (safe_cast rtv rv)
                                        "IntCall cast ret" s6 of
                                   (INL crv, s7) => return (Value crv) s7
                                 | (INR e_v, s7) => (INR e_v, s7))
                            | (INR e_v, s6) => (INR e_v, s6))
                       | (INR e_v, s5) => (INR e_v, s5))
                  | (INR e_v, s4) => (INR e_v, s4))
             | (INR e_v, s3) => (INR e_v, s3))
        | (INR e_v, s2) => (INR e_v, s2))
   | (INR e_v, s1) => (INR e_v, s1)) = (res, st_out) ==>
  state_well_typed st_out /\
  (!crv. res = INL (Value crv) ==> value_has_type ret_tv crv) /\
  (!tv. res = INL tv ==> ?crv. tv = Value crv)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  (* Collapse get_scopes, push_function, return — leave lift_option_type *)
  simp_tac std_ss [get_scopes_def, return_def, push_function_def,
                   pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  (* Layer 1: lift_option_type (bind_arguments ...) *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  simp_tac std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >> gvs[]) >>
  imp_res_tac lift_option_type_SOME >>
  (* Layer 2: lift_option_type (SOME ret_tv) *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  simp_tac std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >> gvs[]) >>
  imp_res_tac lift_option_type_SOME >> BasicProvers.VAR_EQ_TAC >>
  (* Layer 3: lock acquire *)
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lock_acquire_cond_scopes_immutables >>
  simp_tac std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gvs[state_well_typed_def]) >>
  strip_tac >>
  (* At finally level — invoke intcall_finally_swt_vht *)
  irule (GEN_ALL intcall_finally_swt_vht) >>
  qexists `cx with stk updated_by CONS src_fn` >>
  qexists `env_body` >>
  qexists `fn_stmts` >>
  qexists `mut_flag = View \/ mut_flag = Pure` >>
  qexists `nr_flag` >>
  qexists `r'' with scopes := [x]` >>
  qexists `ret_ty_raw` >>
  qexists `r.scopes` >>
  qexists `cx.nonreentrant_slot` >>
  qexists `cx.txn.target` >>
  (* Resolve x' = ret_tv from lift_option_type (SOME ret_tv) *)
  qpat_x_assum `lift_option_type (SOME _) _ _ = _`
    (fn th => SUBST_ALL_TAC
      (SYM (REWRITE_RULE [optionTheory.SOME_11]
        (MATCH_MP lift_option_type_SOME th)))) >>
  (* Side conditions — use stk_irrelevant lemmas to fold, not expand *)
  simp_tac (srw_ss()) [return_def, get_tenv_stk_irrelevant,
    functions_well_typed_stk_irrelevant, context_well_typed_stk_irrelevant] >>
  (* Split into individual side conditions *)
  rpt conj_tac
  >- suspend "swt"
  >- suspend "ih"
  >- suspend "cwt"
  >- suspend "fwt"
  >- suspend "eval_type"
  >- suspend "finally"
  >- suspend "every_swt"
  >- suspend "ec"
  >> suspend "wts"
QED

Resume intcall_chain_swt_vht[swt]:
  irule state_well_typed_with_scopes >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `state_well_typed r`
    (strip_assume_tac o REWRITE_RULE [state_well_typed_def]) >>
  conj_tac
  >- (qpat_x_assum `!sc. _ = SOME sc ==> _` (mp_tac o Q.SPEC `x`) >>
      asm_rewrite_tac [] >> simp_tac (srw_ss()) [])
  >> qpat_x_assum `r''.immutables = r.immutables`
       (fn th => rewrite_tac [th]) >>
     first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[ih]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!env_i ret_ty_i st_i res_i st_i'. _`
    (qspecl_then [`env_i`, `ret_ty_i`, `st_i`, `res_i`, `st_i'`] mp_tac) >>
  simp_tac (srw_ss()) [functions_well_typed_stk_irrelevant,
                        context_well_typed_stk_irrelevant,
                        get_tenv_stk_irrelevant] >>
  disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[cwt]:
  first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[fwt]:
  first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[eval_type]:
  first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[finally]:
  first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[every_swt]:
  first_assum ACCEPT_TAC
QED

Resume intcall_chain_swt_vht[ec]:
  irule env_consistent_scopes_immutables >>
  qexists `r with scopes := [x]` >>
  simp_tac (srw_ss()) [] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >> (qpat_x_assum `!sc. _ = SOME sc ==> _` (mp_tac o Q.SPEC `x`) >>
      asm_rewrite_tac [] >> simp_tac (srw_ss()) [])
QED

Resume intcall_chain_swt_vht[wts]:
  first_assum ACCEPT_TAC
QED

Finalise intcall_chain_swt_vht

Resume eval_preserves_swt[intcall_inl]:
  (* Use suffices_by to bring chain proof to top level *)
  `state_well_typed st' /\
   (!crv. res = INL (Value crv) ==> value_has_type ret_tv crv) /\
   (!tv. res = INL tv ==> ?crv. tv = Value crv)`
    suffices_by (
      strip_tac >>
      pure_rewrite_tac [expr_type_def] >>
      irule (GEN_ALL intcall_inl_wrap) >>
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      qexistsl [`x''0`, `x''1`, `x''2`, `x''3`, `fn`, `x''5`,
                `env.fn_sigs`, `param_types`, `ret_tv`,
                `src_id_opt`, `x'`, `x''4`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Now goal is: swt /\ vht /\ returns_value — at top level *)
  (* Extract clean IH from prefix-wrapped IH *)
  first_assum (mp_tac o REWRITE_RULE [
    check_def, type_check_def, push_function_def, return_def,
    get_scopes_def, lift_option_type_def,
    pairTheory.pair_case_thm, sumTheory.sum_case_def,
    optionTheory.option_case_def]) >>
  simp_tac (srw_ss()) [] >>
  disch_then assume_tac >>
  (* Invoke intcall_chain_swt_vht *)
  irule (GEN_ALL intcall_chain_swt_vht) >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  suspend "chain_sc"
QED

Resume eval_preserves_swt[chain_sc]:
  (* Provide existential witnesses for intcall_chain_swt_vht *)
  qexistsl [`x ++ x''`, `cx`, `env_body`, `x''5`, `x''0`, `x''1`,
            `x''2`, `x''4`, `(src_id_opt, fn)`, `r'`] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  (* Remaining 3 goals: bind_args, IH, EVERY swt *)
  >- suspend "chain_bind"
  >- suspend "chain_ih"
  >> suspend "chain_every_swt"
QED

Resume eval_preserves_swt[chain_bind]:
  strip_tac >> strip_tac >> conj_tac
  >- suspend "chain_bind_swt"
  >> suspend "chain_bind_ec"
QED

Resume eval_preserves_swt[chain_bind_swt]:
  drule (GEN_ALL bind_arguments_scope_well_typed) >>
  disch_then irule >>
  ho_match_mp_tac (GEN_ALL args_dflts_typing_to_el) >>
  qexistsl [`es`, `DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3`] >>
  (* Get param_types = MAP SND x''2 *)
  drule (GEN_ALL fn_sigs_param_types) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  strip_tac >> ntac 2 (pop_assum SUBST_ALL_TAC) >>
  (* Extract length bounds from type_check *)
  first_assum (fn th =>
    if can (match_term ``type_check _ _ _``) (lhs (concl th))
    then mp_tac (SIMP_RULE std_ss [type_check_def, assert_def] th)
    else FAIL_TAC "not type_check") >>
  strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (pure_rewrite_tac [get_tenv_stk_irrelevant] >>
       first_assum ACCEPT_TAC) >>
  TRY (irule dflts_drop_length_match >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC)) >>
  irule dflts_drop_types_match >> rpt conj_tac >>
  first_assum ACCEPT_TAC
QED

Resume eval_preserves_swt[chain_bind_ec]:
  drule (GEN_ALL bind_arguments_env_consistent) >>
  disch_then irule >>
  first_assum (fn th =>
    if can (match_term ``(eb:typing_env).fn_sigs = _``) (concl th)
    then pure_rewrite_tac [th] else NO_TAC) >>
  pure_rewrite_tac [get_tenv_stk_irrelevant, get_module_code_stk_irrelevant,
                    fn_sigs_consistent_stk_irrelevant,
                    evaluation_context_accfupds] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY REFL_TAC
QED
Resume eval_preserves_swt[chain_ih]:
  (* ML-level tactic: SPECL the chain-prefix IH with 33 witnesses,
     derive bind_arguments = SOME, then discharge 12 conditions. *)
  (fn (asl, gl) => let
    val ih_tm = List.nth(asl, 1)
    val ih = ASSUME ih_tm
    fun fa pat = valOf (List.find (fn a => can (match_term pat) a) asl)
    fun fa_filt pat pred = valOf (List.find (fn a =>
      can (match_term pat) a andalso pred a) asl)
    fun fa_3rd_arg target = valOf (List.find (fn a =>
      can (match_term ``LIST_REL _ _ _``) a andalso
      (let val (_, args) = strip_comb a
       in length args = 3 andalso aconv (List.nth(args, 2)) target end
       handle _ => false)) asl)
    val arb_s = mk_arb ``:evaluation_state``
    val arb_u = mk_arb ``:unit``
    val ts_v = rand (rhs (concl (ASSUME (fa ``get_module_code cx src_id_opt = SOME _``))))
    val tup_v = rand (rhs (concl (ASSUME (fa ``lookup_callable_function _ _ _ = SOME _``))))
    val ee1 = fa_filt ``eval_exprs cx es _ = (INL _, _)``
      (fn a => not (can (match_term ``eval_exprs (cx with stk updated_by _) _ _ = _``) a))
    val ee2 = fa ``eval_exprs (cx with stk updated_by _) _ _ = (INL _, _)``
    fun dest_pe a = let val (l,r) = dest_eq a val (res,out) = pairSyntax.dest_pair r
                    in (rand l, rand res, out) end
    val (e1s, e1v, e1o) = dest_pe ee1
    val (_, e2v, e2o) = dest_pe ee2
    val ret_tv_v = rand (rhs (concl (ASSUME
      (fa ``evaluate_type (get_tenv cx) x''4 = SOME _``))))
    val ba = ``bind_arguments (get_tenv cx) x''2 (^e1v ++ ^e2v)``
    val zero_s = ``(ARB:evaluation_state) with tStorage := (\a sv. (0w:256 word))``
    val lock_e = ``(if x''1 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
             (x''0 = View \/ x''0 = Pure)
       else return ())``
    val lk_out = ``SND (^lock_e ^zero_s)``
    val cx_p = ``cx with stk updated_by CONS (src_id_opt,fn)``
    val push_o = ``^lk_out with scopes := [THE ^ba]``
    val specs = [
      arb_s, arb_u, arb_s, arb_s, ts_v, arb_s, arb_s,
      tup_v, arb_s, arb_s, arb_u, arb_s,
      e1s, e1v, e1o, e1o, e2v, e2o,
      arb_s, ``THE ^ba``, arb_s, arb_s,
      ``(ARB:evaluation_state).scopes``, arb_s,
      arb_s, ret_tv_v, arb_s,
      zero_s, arb_u, lk_out, lk_out, cx_p, push_o
    ]
    val ih2 = SIMP_RULE std_ss [] (SPECL specs ih)
    (* Derive bind_arguments = SOME *)
    val fsc_a = fa ``fn_sigs_consistent env.fn_sigs cx``
    val flk_a = fa ``FLOOKUP env.fn_sigs (src_id_opt,fn) = SOME _``
    val gmc_a = fa ``get_module_code cx src_id_opt = SOME _``
    val lcf_a = fa ``lookup_callable_function _ _ _ = SOME _``
    val pt_eq = CONJUNCT1 (MATCH_MP fn_sigs_param_types
      (LIST_CONJ (map ASSUME [fsc_a, flk_a, gmc_a, lcf_a])))
    val tc_a = fa ``type_check _ _ _ = (INL _, _)``
    val tc_s = SIMP_RULE std_ss [type_check_def, assert_def] (ASSUME tc_a)
    val l1 = CONJUNCT1 (UNDISCH_ALL tc_s)
    val l2 = CONJUNCT2 (UNDISCH_ALL tc_s)
    val met_es = REWRITE_RULE [pt_eq]
      (ASSUME (fa ``MAP expr_type es = TAKE _ param_types``))
    val met_x3 = ASSUME (fa ``MAP expr_type x''3 = MAP SND (DROP _ x''2)``)
    val c4 = MATCH_MP dflts_drop_types_match (LIST_CONJ [met_x3, l1, l2])
    val c5 = MATCH_MP dflts_drop_length_match (LIST_CONJ [met_x3, l1, l2])
    val lrel1 = ASSUME (fa_3rd_arg ``es:expr list``)
    val lrel2 = ASSUME (fa ``LIST_REL _ x'' (DROP _ x''3)``)
    val ba_some = MATCH_MP args_dflts_bind_arguments
      (LIST_CONJ [lrel1, lrel2, met_es, c4, c5])
    in (mp_tac ih2 >> strip_assume_tac ba_some) (asl, gl) end) >>
  (* Discharge 12 chain-prefix conditions *)
  impl_tac >- (
    (fn (asl, gl) => let
      val some_ths = map ASSUME (List.filter (fn a =>
        can (match_term ``_ = SOME _``) a) asl)
      val eval_ths = map ASSUME (List.filter (fn a =>
        can (match_term ``eval_exprs _ _ _ = (INL _, _)``) a) asl)
      val check_th = SIMP_RULE std_ss [check_def, assert_def]
        (ASSUME (valOf (List.find (fn a =>
          can (match_term ``check _ _ _ = (INL _, _)``) a) asl)))
      val tc_th = SIMP_RULE std_ss [type_check_def, assert_def]
        (ASSUME (valOf (List.find (fn a =>
          can (match_term ``type_check _ _ _ = (INL _, _)``) a) asl)))
      val arb_unit_thm = prove(``() = (ARB:unit)``,
        Cases_on `ARB:unit` >> rewrite_tac[])
      val rws = [check_def, assert_def, type_check_def,
        lift_option_type_def, return_def, get_scopes_def,
        push_function_def, option_case_def, arb_unit_thm,
        check_th, tc_th] @ some_ths @ eval_ths
      in simp_tac std_ss rws (asl, gl) end) >>
    (* Remaining: lock equality *)
    CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [GSYM PAIR])) >>
    cong_tac (SOME 1) >>
    (* FST(lock_expr zero_st) = INL () *)
    IF_CASES_TAC >- (
      (* x''1 = T: lock must succeed *)
      first_assum (fn th1 =>
        first_assum (fn th2 =>
          if aconv (concl th1) ``x''1:bool`` andalso
             can (match_term ``x''1 ==> _``) (concl th2)
          then mp_tac (MP th2 th1) else FAIL_TAC "")) >>
      strip_tac >>
      Cases_on `cx.nonreentrant_slot` >-
        (pop_assum mp_tac >> pop_assum mp_tac >> simp_tac std_ss []) >>
      simp_tac std_ss [option_case_def] >>
      simp_tac (srw_ss() ++ wordsLib.WORD_ss)
        [acquire_nonreentrant_lock_def, get_transient_storage_def,
         return_def, bind_def, ignore_bind_def, raise_def, LET_THM,
         vfmStateTheory.lookup_storage_def,
         vfmExecutionTheory.lookup_transient_storage_def,
         pairTheory.pair_case_thm] >>
      IF_CASES_TAC >>
      simp_tac (srw_ss()) [return_def, update_transient_def]
    ) >>
    simp_tac std_ss [return_def]
  ) >>
  disch_then ACCEPT_TAC
QED

Resume eval_preserves_swt[chain_every_swt]:
  drule (iffLR state_well_typed_def) >> strip_tac
QED

Resume eval_preserves_swt[RawCallTarget]:
  tp_chain_prefix_tac ev_RawCallTarget wte_RawCallTarget >>
  tp_chain_tail_tac default_chain_value_tac
QED

Resume eval_preserves_swt[RawLog]:
  tp_chain_prefix_tac ev_RawLog wte_RawLog >>
  tp_chain_tail_tac (TRY DECIDE_TAC)
QED

Resume eval_preserves_swt[RawRevert]:
  tp_chain_prefix_tac ev_RawRevert wte_RawRevert >>
  tp_chain_tail_tac (TRY DECIDE_TAC)
QED

Resume eval_preserves_swt[SelfDestructTarget]:
  tp_chain_prefix_tac ev_SelfDestructTarget wte_SelfDestructTarget >>
  tp_chain_tail_tac (TRY DECIDE_TAC)
QED

Resume eval_preserves_swt[CreateTarget]:
  tp_chain_prefix_tac ev_CreateTarget wte_CreateTarget >>
  tp_chain_tail_tac default_chain_value_tac
QED

Resume eval_preserves_swt[exprs_cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_exprs _ (_::_)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wte_exprs_cons]) >>
  qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
  rewrite_tac[ev_exprs_cons] >>
  simp_tac std_ss [bind_apply, BETA_THM] >>
  (* Step 1: eval_expr cx e *)
  Cases_on `eval_expr cx e st` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* Apply P7 IH for e *)
  first_x_assum drule_all >> strip_tac >>
  (* Step 2: materialise *)
  Cases_on `materialise cx x r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* Step 3: eval_exprs cx es (guarded IH) *)
  imp_res_tac materialise_state >> rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `eval_exprs cx es r` >>
  reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
  TRY (tp_bind_err_tac >> NO_TAC) >>
  (* Apply guarded P8 IH: guard is eval_expr + materialise *)
  first_x_assum
    (qspecl_then [`st`, `x`, `r`, `r`, `x'`, `r`] mp_tac) >>
  simp_tac (srw_ss()) [] >>
  disch_then drule_all >> strip_tac >>
  (* return (v::vs) *)
  simp_tac (srw_ss()) [return_def] >>
  tp_bind_err_tac >>
  (* Value typing: LIST_REL for v::vs *)
  tp_materialise_conclusion_tac >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qexistsl_tac [`x'`, `x''`] >> simp[]
QED

Finalise eval_preserves_swt



(* ===== COUNTEREXAMPLE: type_preservation P7 is FALSE ===== *)
(*
 * The expression Builtin (BaseT (UintT 256)) (Env TimeStamp) []
 * is well-typed, but when cx.txn.time_stamp = 2^256 (which no hypothesis
 * constrains), eval_expr returns IntV (&(2^256)) which does NOT satisfy
 * value_has_type (BaseTV (UintT 256)).
 *
 * Root cause: Env builtins read unbounded num fields from cx.txn.
 * Fix: add a context_well_typed hypothesis constraining cx.txn fields.
 *)

(* Concrete witness values *)
val ce_env_def = Define `
  ce_env = <| var_types := FEMPTY; global_types := FEMPTY;
              toplevel_types := FEMPTY; type_defs := FEMPTY;
              fn_sigs := FEMPTY; flag_members := FEMPTY |>`;

val ce_acct_def = Define `
  ce_acct = <| nonce := 0; balance := 0; storage := K 0w; code := [] |>`;

val ce_st_def = Define `
  ce_st = <| immutables := []; logs := []; scopes := [FEMPTY];
             accounts := K ce_acct; tStorage := K (K 0w) |>`;

val ce_txn_def = Define `
  ce_txn = <| sender := 0w; target := 0w; function_name := "";
              args := []; value := 0; time_stamp := 2 ** 256;
              block_number := 0; block_hashes := []; blob_hashes := [];
              blob_base_fee := 0; gas_price := 0; chain_id := 0;
              is_creation := F; coinbase := 0w; gas_limit := 0;
              base_fee := 0; prev_randao := 0; origin := 0w |>`;

val ce_cx_def = Define `
  ce_cx = <| stk := []; txn := ce_txn; sources := []; layouts := [];
             in_deploy := F; nonreentrant_slot := NONE |>`;

val ce_expr_def = Define `
  ce_expr = Builtin (BaseT (UintT 256)) (Env TimeStamp) []`;

(* All hypotheses of type_preservation P7 hold *)
Theorem ce_hypotheses_hold:
  well_typed_expr ce_env ce_expr /\
  env_consistent ce_env ce_cx ce_st /\
  state_well_typed ce_st /\
  functions_well_typed ce_cx
Proof
  rpt CONJ_TAC >> EVAL_TAC >> simp[]
QED

(* eval_expr succeeds, materialise succeeds, but value is NOT well-typed *)
Theorem ce_eval_result:
  eval_expr ce_cx ce_expr ce_st =
    (INL (Value (IntV (&(2 ** 256)))), ce_st)
Proof
  EVAL_TAC
QED

Theorem ce_materialise_result:
  materialise ce_cx (Value (IntV (&(2 ** 256)))) ce_st =
    (INL (IntV (&(2 ** 256))), ce_st)
Proof
  EVAL_TAC
QED

Theorem ce_type_result:
  evaluate_type (get_tenv ce_cx) (expr_type ce_expr) =
    SOME (BaseTV (UintT 256))
Proof
  EVAL_TAC
QED

(* The conclusion of P7 fails: value does not have the declared type *)
Theorem ce_conclusion_fails:
  ~value_has_type (BaseTV (UintT 256)) (IntV (&(2 ** 256)))
Proof
  EVAL_TAC
QED

(* Combined: type_preservation P7 is false *)
Theorem type_preservation_P7_counterexample:
  ~(!cx e. !env st res st'.
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
                 value_has_type tyv v))))
Proof
  simp[] >>
  qexistsl_tac [`ce_cx`, `ce_expr`, `ce_env`, `ce_st`,
    `INL (Value (IntV (&(2 ** 256))))`, `ce_st`] >>
  simp[ce_hypotheses_hold, ce_eval_result] >>
  simp[ce_materialise_result, ce_type_result, ce_hypotheses_hold] >>
  EVAL_TAC
QED


(* ===== type_preservation: derived from eval_preserves_swt ===== *)
(* Requires context_well_typed cx — see counterexample above for why (ce — value_preservation P7 fails without it).
   Includes no-TypeError (type soundness / progress): well-typed programs
   never raise TypeError exceptions.
   P2 (eval_iterator) drops well_typed_iterator; swt+ec follow from swt P2
   which is strictly stronger. *)

Theorem type_preservation:
  (* P0: eval_stmt *)
  (!cx s. !env ret_ty st res st'.
    well_typed_stmt env ret_ty s /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (* P1: eval_stmts *)
  (!cx ss. !env ret_ty st res st'.
    well_typed_stmts env ret_ty ss /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (* P2: eval_iterator *)
  (!cx it. !env typ st res st'.
    well_typed_iterator env typ it /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P3: eval_target *)
  (!cx g. !env st res st'.
    (?ty. well_typed_atarget env g ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_target cx g st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P4: eval_targets *)
  (!cx gs. !env st res st'.
    EVERY (\g. ?ty. well_typed_atarget env g ty) gs /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_targets cx gs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P5: eval_base_target *)
  (!cx bt. !env st res st'.
    (?ty. well_typed_target env bt ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (* P6: eval_for *)
  (!cx tyv nm body vs. !env typ ret_ty st res st'.
    well_typed_stmts (env with var_types updated_by (flip FUPDATE (nm, typ)))
                     ret_ty body /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    nm NOTIN FDOM env.var_types /\
    eval_for cx tyv nm body vs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
               evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
               value_has_type ret_tv v)) /\
  (* P7: eval_expr *)
  (!cx e. !env st res st'.
    well_typed_expr env e /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_expr cx e st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!tv. res = INL tv ==>
       (!v st''. materialise cx tv st' = (INL v, st'') ==>
          state_well_typed st'' /\ env_consistent env cx st'' /\
          (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv v)))) /\
  (* P8: eval_exprs *)
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!vs. res = INL vs ==>
      LIST_REL (\v e. ?tyv.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
        value_has_type tyv v) vs es))
Proof
  rpt CONJ_TAC
  (* P0 *) >- metis_tac[cj 1 eval_preserves_swt]
  (* P1 *) >- metis_tac[cj 2 eval_preserves_swt]
  (* P2 *) >- metis_tac[cj 3 eval_preserves_swt]
  (* P3 *) >- metis_tac[cj 4 eval_preserves_swt]
  (* P4 *) >- metis_tac[cj 5 eval_preserves_swt]
  (* P5 *) >- metis_tac[cj 6 eval_preserves_swt]
  (* P6 *) >- metis_tac[cj 7 eval_preserves_swt]
  (* P7: type_preservation P7 is strictly weaker than eval_preserves_swt P8
     (drops toplevel_value_typed conjunct) *)
  >- (rpt gen_tac >> strip_tac >>
      drule_all (cj 8 eval_preserves_swt) >> metis_tac[])
  (* P8 *) >> metis_tac[cj 9 eval_preserves_swt]
QED
