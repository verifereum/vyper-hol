(* Body simulation by the interpreter's termination measure.  In particular,
   ABI traversal need not imply ordinary-evaluation reachability: the ordinary
   simulation of each operand is available at its strictly smaller bound. *)
Theory bodySimBound
Ancestors
  arithmetic list rich_list alist pair option vyperMisc vyperValue
  bodySim bodySimStmtCases bodySimExprCases stmtSimIf supportedStmts vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeCallGraph

(* ===== Numeric loop bound ===== *)

Theorem body_loop_bound[local]:
  !len nb sz itb. len <= nb ==>
    len + (len * sz + 1) < nb + (nb * sz + (itb + 2))
Proof
  rpt strip_tac >>
  drule_then (qspec_then `sz` mp_tac) LESS_MONO_MULT >> decide_tac
QED

(* ===== Induction tactics ===== *)

(* The ten judgments use the same weights as evaluate's termination proof.
   eval_base_place and eval_target_place share one judgment. *)
val body_bounds =
  [(``body_stmt_ok``, ``\cx s. 4 * stmt_bound (remcode cx) s``),
   (``body_stmts_ok``, ``\cx ss. 4 * stmts_bound (remcode cx) ss``),
   (``body_iterator_ok``, ``\cx it. 4 * iterator_bound (remcode cx) it``),
   (``body_for_ok``, ``\cx (tyv : type_value) (nm : identifier) body (vs : value list).
       4 * (1 + LENGTH vs + LENGTH vs * stmts_bound (remcode cx) body)``),
   (``body_expr_ok``, ``\cx e. 4 * expr_bound (remcode cx) e``),
   (``body_exprs_ok``, ``\cx es. 4 * exprs_bound (remcode cx) es``),
   (``body_base_target_ok``, ``\cx t. 4 * base_target_bound (remcode cx) t``),
   (``body_tuple_target_ok``, ``\cx g (v : value). 4 * target_bound (remcode cx) g + 2``),
   (``body_tuple_targets_ok``, ``\cx gs (vs : value list). 4 * targets_bound (remcode cx) gs + 2``),
   (``body_results_ok``, ``\cx es. 4 * exprs_bound (remcode cx) es``)];

(* Apply the appropriate conjunct of complete induction, leaving only its
   strict bound inequality.  No semantic judgment is unfolded here. *)
fun BODY_BOUND_IH_TAC (asl,w) = let
  val (head,args) = strip_comb w
  fun index k [] = raise mk_HOL_ERR "bodySimBound" "BODY_BOUND_IH_TAC" "not a body judgment"
    | index k ((p,_)::ps) = if same_const head p then k else index (k+1) ps
  val i = index 0 body_bounds
  val bound = rhs (concl (DEPTH_CONV BETA_CONV
    (list_mk_comb (#2 (List.nth(body_bounds,i)),args))))
  val ih = first (fn th => is_forall (concl th) andalso
    is_imp (snd (dest_forall (concl th))) andalso
    is_conj (#2 (dest_imp (snd (dest_forall (concl th)))))) (map ASSUME asl)
  val spec = SPEC bound ih
  val premise = #1 (dest_imp (concl spec))
  val part = List.nth (CONJUNCTS (UNDISCH spec),i)
  val result = MP (SPECL args part) (REFL bound)
 in (MATCH_MP_TAC (DISCH premise result) >>
     qpat_x_assum `!m. _` kall_tac) (asl,w) end;

val BODY_BOUND_SIMPLE_TAC =
  gvs[bound_def, MAX_DEF, MULT, IS_SOME_EXISTS,
      compatible_bound_def, check_def, type_check_def, assert_def,
      builtin_args_length_ok_def, type_builtin_args_length_ok_def,
      LENGTH_EQ_NUM_compute];

val BODY_BOUND_OPERANDS_TAC =
  irule LESS_EQ_LESS_TRANS >>
  qexists_tac `exprs_bound (remcode cx) es` >>
  simp[exprs_bound_TAKE_DROP, exprs_bound_TAKE, exprs_bound_DROP, DROP_DROP_T];

val BODY_BOUND_CALL_TAC =
  qmatch_asmsub_rename_tac
    `lift_option_type (lookup_callable_function _ _ _) _ _ = (INL callable,_)` >>
  PairCases_on `callable` >>
  gvs[check_def, type_check_def, assert_def, push_function_def, return_def] >>
  gvs[lift_option_def, lift_option_type_def, CaseEq"option", CaseEq"prod",
      option_CASE_rator, raise_def, return_def] >>
  gvs[remcode_def, get_module_code_def, ADELKEY_def] >>
  TRY (qpat_x_assum `OUTR _ _ = _` kall_tac) >> gvs[CaseEq"option"] >>
  simp[bound_def] >>
  qmatch_asmsub_rename_tac
    `lookup_callable_function _ fn ts = SOME (_, _, args, dflts, ret, bdy)` >>
  Cases_on `(dflts, bdy) = ([], [])` >- gvs[bound_def] >>
  `(dflts, bdy) <> ([], [])` by (strip_tac >> gvs[]) >>
  drule_all_then(qspec_then `src_id_opt` strip_assume_tac)
    lookup_callable_function_eq_ALOOKUP_module_fns >>
  drule_at_then Any drule ALOOKUP_FLAT_MAP_module_fns >>
  qmatch_goalsub_abbrev_tac `ALOOKUP (FILTER P ls) k` >>
  `P = λ(k,v). ~MEM k cx.stk` by simp[Abbr`P`, FUN_EQ_THM, FORALL_PROD] >>
  TRY (simp[ALOOKUP_FILTER, FILTER_FILTER, Abbr`k`] >> simp[LAMBDA_PROD] >>
    qmatch_goalsub_abbrev_tac `exprs_bound fts (DROP n dflts)` >>
    qspecl_then [`fts`, `n`, `dflts`] mp_tac exprs_bound_DROP >> simp[] >> NO_TAC) >>
  pop_assum SUBST_ALL_TAC >> simp[ALOOKUP_FILTER] >>
  rw[FILTER_FILTER, UNCURRY, Abbr`k`] >> simp[LAMBDA_PROD];

val BODY_BOUND_CLOSE_TAC =
  simp[] >> rpt strip_tac >> BODY_BOUND_IH_TAC >>
  BODY_BOUND_SIMPLE_TAC >> FIRST [BODY_BOUND_CALL_TAC, BODY_BOUND_OPERANDS_TAC];

fun BODY_SOLVE tacs = FIRST (map (fn tac => tac >> NO_TAC) tacs);

val body_stmt_cases =
 [body_pass_case, body_continue_case, body_break_case, body_return_none_case,
  body_return_case, body_raise_reason_case, body_assert_case,
  body_assert_reason_case, body_log_case, body_annassign_case, body_append_case,
  body_assign_case, body_assign_tuple_case, body_augassign_case, body_if_case,
  body_for_case, body_expr_stmt_case];
val body_expr_cases =
 [body_ifexp_case, body_structlit_case, body_subscript_case, body_attribute_case,
  body_builtin_case, body_pop_case, body_type_builtin_case, body_send_case,
  body_extcall_case, body_intcall_case, body_raw_call_case,
  body_raw_call_calldata_case, body_raw_log_case, body_raw_revert_case,
  body_selfdestruct_case, body_create_case];

(* ===== The bounded simulation ===== *)

Theorem body_sim_bounded:
  !n.
  (!cx s. 4 * stmt_bound (remcode cx) s = n ==> body_stmt_ok cx s) /\
  (!cx ss. 4 * stmts_bound (remcode cx) ss = n ==> body_stmts_ok cx ss) /\
  (!cx it. 4 * iterator_bound (remcode cx) it = n ==> body_iterator_ok cx it) /\
  (!cx tyv nm body vs.
     4 * (1 + LENGTH vs + LENGTH vs * stmts_bound (remcode cx) body) = n ==>
     body_for_ok cx tyv nm body vs) /\
  (!cx e. 4 * expr_bound (remcode cx) e = n ==> body_expr_ok cx e) /\
  (!cx es. 4 * exprs_bound (remcode cx) es = n ==> body_exprs_ok cx es) /\
  (!cx t. 4 * base_target_bound (remcode cx) t = n ==> body_base_target_ok cx t) /\
  (!cx g v. 4 * target_bound (remcode cx) g + 2 = n ==> body_tuple_target_ok cx g v) /\
  (!cx gs vs. 4 * targets_bound (remcode cx) gs + 2 = n ==>
     body_tuple_targets_ok cx gs vs) /\
  (!cx es. 4 * exprs_bound (remcode cx) es = n ==> body_results_ok cx es)
Proof
  completeInduct_on `n` >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `s`
      >~ [`body_stmt_ok _ (For _ _ _ _ _)`]
      >- (irule body_for_case >> rpt strip_tac >> BODY_BOUND_IH_TAC >>
          BODY_BOUND_SIMPLE_TAC >> irule body_loop_bound >> simp[]) >>
      TRY (rename1 `Return eo` >> Cases_on `eo`) >>
      TRY (rename1 `Raise reason` >> Cases_on `reason`) >>
      TRY (rename1 `Assert e reason` >> Cases_on `reason`) >>
      TRY (rename1 `Assign target e` >> Cases_on `target`) >>
      BODY_SOLVE (map (fn th => irule th >> BODY_BOUND_CLOSE_TAC) body_stmt_cases @
       [rw[body_stmt_ok_def] >> irule compile_raise_frag >> simp[],
        rw[body_stmt_ok_def, supported_stmt_def, supported_raise_reason_def,
           supported_assert_reason_def]]))
  >- (Cases_on `ss` >> BODY_SOLVE (map (fn th => irule th >> BODY_BOUND_CLOSE_TAC)
        [body_stmts_nil_case, body_stmts_cons_case]))
  >- (Cases_on `it` >> rw[body_iterator_ok_def] >>
      BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC)
  >- (Cases_on `vs` >> rw[body_for_ok_def] >>
      BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC)
  >- (Cases_on `e` >>
      TRY (rename1 `Builtin ann bt es`) >>
      TRY (rename1 `TypeBuiltin ann tb typ es`) >>
      TRY (rename1 `Call ann target es dflt` >> Cases_on `target`) >>
      TRY (rename1 `IntCall nsid` >> Cases_on `nsid` >>
           rename1 `IntCall (src_id_opt,fn)`) >>
      TRY (rename1 `ExtCall _ _ sig _` >> PairCases_on `sig`) >>
      TRY (rename1 `StructLit _ nsid _` >> Cases_on `nsid`) >>
      TRY (irule body_expr_ok_intro >> simp[int_calls_expr_def] >> NO_TAC) >>
      FIRST (map irule body_expr_cases) >> BODY_BOUND_CLOSE_TAC)
  >- (Cases_on `es` >> rw[body_exprs_ok_def] >>
      BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC)
  >- (Cases_on `t` >> rw[body_base_target_ok_def] >>
      BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC)
  >- (Cases_on `g` >> rw[body_tuple_target_ok_def] >>
      BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC)
  >- (Cases_on `gs` >> Cases_on `vs` >> rw[body_tuple_target_ok_def] >>
      BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC) >>
  Cases_on `es` >> rw[body_results_ok_def] >> BODY_BOUND_IH_TAC >> BODY_BOUND_SIMPLE_TAC
QED
