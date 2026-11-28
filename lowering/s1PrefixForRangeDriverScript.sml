(* Request-prefix Range driver, sharing the full driver's setup and layout. *)
Theory s1PrefixForRangeDriver
Ancestors
  bodyFullForRange bodyFullPreds loweringPosts stmtSimDefs stmtSimProps
  s1PrefixForRangeCons s1PrefixForRounds s1PrefixDefs s1PrefixPreds
  s1PrefixFrame s1PrefixCompose s1PrefixInvalidTraceDomain s1PrefixProps stmtSimForRange
  bodyFullShared[qualified,ignore_grammar] vyperStorageTrace vyperState
  vyperInterpreter vyperAST gasOutcomeFull gasShadow gasCount gasEvents
  fragGasOriginPtr fragGasPathPtr vyperStorageFootprint venomState
  loweringStateRelDefs stmtSimForParts list
  bodyFullPredsMods[qualified]
Libs rangeForDriverLib[qualified] rangeRoundEntryLib[qualified]

val _ = Parse.hide "body";

(* The two source guards are the prefix counterparts of the full guards.
   Keep the remaining outer hypotheses and the invocation as in the full
   driver, using the named fragment precondition. *)
local
  val (args, rule) = strip_forall (concl compile_for_range_frag_full)
  val (pre, full) = dest_imp rule
  val (head, actuals) = strip_comb full
  val _ = if same_const head ``stmt_frag_full`` then ()
          else raise Fail "Expected the full Range fragment"
  fun prefix_guard clause =
    let
      val (vars, conditional) = strip_forall clause
      val (ante, result) = dest_imp conditional
      val (pred, xs) = strip_comb result
      val prefix =
        if same_const pred ``body_for_full_ok_mods`` then ``body_for_prefix_ok``
        else if same_const pred ``body_iterator_full_ok_mods`` then ``body_iterator_prefix_ok``
        else raise Fail "Expected a guarded Range IH"
    in list_mk_forall (vars, mk_imp (ante, list_mk_comb (prefix, List.drop (xs, 2)))) end
  val clauses = strip_conj pre
  val guards = List.take (List.drop (clauses, 4), 2)
  val invocation = rhs (concl (PURE_REWRITE_CONV [stmt_frag_prefix_def]
      (boolSyntax.list_mk_icomb (``stmt_frag_prefix``, actuals))))
in
  val range_driver_prefix_statement = list_mk_forall (args,
    mk_imp (list_mk_conj (clauses @ map prefix_guard guards), invocation))
end

fun range_endpoint_prefix_tac child_ok source entry_args ready =
  qpat_assum child_ok
    (mp_tac o CONJUNCT1 o PURE_ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
      `func`,`shadow_func`,`cenv`,`env`,`typ`,source] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1 o BETA_RULE) >>
  pure_once_rewrite_tac [expr_sim_prefix_def] >>
  disch_then (qspecl_then (`st0` :: entry_args) mp_tac) >>
  impl_tac >- (pure_once_rewrite_tac [expr_sim_full_pre_def] >> ready) >>
  disch_tac;

val range_first_prefix_tac =
  qpat_assum `!tenv s'' tyv t. _ ==> body_iterator_prefix_ok _ _`
    (qspecl_then [`get_tenv cx`,`es`,`tyv`,`es`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  pure_once_rewrite_tac [body_iterator_prefix_ok_def] >> strip_tac >>
  range_endpoint_prefix_tac `body_expr_prefix_ok cx e1` `es`
    [`sa`,`s1`,`shadow_sa`,`shadow_s1`,`op1`,`s0`,`G0`,`tn0`]
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
      goal_assum (drule_at Any)]);

fun range_storage_frame_tac g =
  (FIRST [first_assum ACCEPT_TAC,
          simp[NoAsms, evaluate_storage_trace_frame, storage_trace_frame_read_result,
              storage_trace_frame_lifts, storage_trace_frame_checks, storage_trace_frame_return] >> NO_TAC,
          irule storage_trace_frame_bind_all >> conj_tac >>
            TRY gen_tac >> BETA_TAC >> range_storage_frame_tac,
          irule storage_trace_frame_ignore_bind >> conj_tac >> range_storage_frame_tac]) g;

fun range_prefix_bind_tac outcome prefix exceptional requests =
  qpat_assum outcome (mp_then Any irule gas_prefix_full_bind_replay) >>
  BETA_TAC >>
  reverse (rpt conj_tac)
  >- prefix
  >- range_storage_frame_tac
  >- requests
  >- (gen_tac >> range_storage_frame_tac)
  >- exceptional >>
  SIMP_TAC std_ss [sumTheory.INL_11];

val range_split_midpoint_tac =
  qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (strip_assume_tac o PURE_REWRITE_RULE [GSYM CONJ_ASSOC] o
     SIMP_RULE pure_ss [Once IMP_CONJ_THM, Once FORALL_AND_THM]);

fun range_normal_post_tac source states =
  let
    val stem = `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
                     (cx_tops cx) cx st0 (` @ source @ `) (` @ states @ `) `
    val outcome = stem @ `Q0 R0`
  in
    qmatch_asmsub_abbrev_tac outcome >>
    sg (stem @ `(\H res ee G tn t. Q0 H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted) R0`) >-
      (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
       qpat_assum outcome (irule_at Any) >> BETA_TAC >>
       rpt conj_tac >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
    qpat_x_assum outcome kall_tac >> unabbrev_all_tac
  end;

val range_endpoint_requests_tac =
  irule requests_outcomes_frame_bind_all >>
  simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result];

val range_endpoint_exit_tac =
  rpt gen_tac >> Cases_on `res` >> simp[NoAsms, exprSimDefsTheory.expr_exit_INL];

(* Specialize the prefix cons rule before the two initializer branches
   consume their local code equations. This binds no further layout. *)
val range_driver_prefix_cons_tac =
  let
    val (static, imp) = strip_forall (concl range_cons_prefix)
    val (layout, _) = strip_forall (snd (dest_imp imp))
    fun args vars = map (fn v =>
      let val (name, _) = dest_var v in [QUOTE (if name = "bound" then "n" else name)] end) vars
  in
    qspecl_then (args static) (mp_tac o BETA_RULE o PURE_ONCE_REWRITE_RULE [LET_THM])
      range_cons_prefix >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then (args layout) mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (mk_asm "round_prefix")
  end;

Theorem range_frag_prefix_from_cons:
  ^range_driver_prefix_statement
Proof
  rpt gen_tac >>
  (* The generated statement quantifies both the outer and invocation variables
     on opposite sides of the outer implication. *)
  disch_then (fn th =>
    let val clauses = CONJUNCTS th in
      EVERY (map assume_tac clauses) >> mk_asm "frame_comp" (hd clauses)
    end) >>
  rpt gen_tac >> simp[NoAsms, stmt_frag_full_pre_def] >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (rangeForDriverLib.range_driver_static_tac range_full_outer_env range_full_static_pre >>
      rangeForDriverLib.range_driver_layout_tac
        (mp_tac range_full_round_with_entry >>
         impl_tac >- (conj_tac >- ACCEPT_TAC range_full_body_entry >>
                      rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      range_driver_prefix_cons_tac >>
      rangeForDriverLib.range_driver_cases_tac (suspend "literal") (suspend "computed")) >>
  irule gas_prefix_full_invalid_trace_domain >>
  asm_rewrite_tac [] >> simp[evaluate_storage_trace_frame]
QED

Resume range_frag_prefix_from_cons[computed]:
  rangeForDriverLib.range_checked_shadow_edges_tac >>
  rangeForDriverLib.range_checked_code_tac >>
  rangeForDriverLib.range_checked_source_tac >>
  rangeForDriverLib.range_first_endpoint_tac >> range_first_prefix_tac >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `sa`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas) >>
  range_normal_post_tac `bind (eval_expr cx e1) (read_result cx)` `es,s0,G0,tn0` >>
  rangeForDriverLib.range_computed_eval_tac >>
  pop_assum (fn eq => mk_asm "computed_eval" eq >> SUBST1_TAC eq) >>
  range_prefix_bind_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0) _ _`
    (first_assum ACCEPT_TAC) range_endpoint_exit_tac range_endpoint_requests_tac >>
  map_every qx_gen_tac [`marks1`,`v1`,`mid1`,`G1`,`tn1`,`t1`] >> strip_tac >>
  range_split_midpoint_tac >>
  suspend "second"
QED

Resume range_frag_prefix_from_cons[second]:
  rangeForDriverLib.range_first_replay_tac >>
  `body_expr_full_ok cx e2` by
    (rangeForDriverLib.range_second_guard_tac
      `(?s tv t s1 v t1. eval_expr cx e1 s = _ /\ _) ==> body_expr_full_ok cx e2`) >>
  `body_expr_prefix_ok cx e2` by
    (rangeForDriverLib.range_second_guard_tac
      `(?s tv t s1 v t1. eval_expr cx e1 s = _ /\ _) ==> body_expr_prefix_ok cx e2`) >>
  rangeForDriverLib.range_second_pre_tac >>
  rangeForDriverLib.range_second_endpoint_tac rangeForDriverLib.range_second_entry_tac >>
  range_endpoint_prefix_tac `body_expr_prefix_ok cx e2` `mid1`
    [`s1`,`st`,`shadow_s1`,`shadow_st`,`op2`,`t1`,`G1`,`tn1`]
    rangeForDriverLib.range_second_entry_tac >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `s1`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas_from) >>
  range_normal_post_tac `bind (eval_expr cx e2) (read_result cx)` `mid1,t1,G1,tn1` >>
  range_prefix_bind_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e2) (read_result cx)) (mid1,t1,G1,tn1) _ _`
    (first_assum ACCEPT_TAC) range_endpoint_exit_tac range_endpoint_requests_tac >>
  map_every qx_gen_tac [`marks2`,`v2`,`mid2`,`G2`,`tn2`,`t2`] >> strip_tac >>
  range_split_midpoint_tac >>
  rangeForDriverLib.range_checked_read_tac >>
  rangeForDriverLib.range_checked_frame_tac >>
  rangeForDriverLib.range_checked_operands_tac >>
  rangeForDriverLib.range_fresh_scope_tac `mid2` >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ (bind (eval_expr _ _) _) _ _ _` kall_tac) >>
  rpt (qpat_x_assum `gas_prefix_full _ _ _ (bind (eval_expr _ _) _) _` kall_tac) >>
  rpt (qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _` kall_tac) >>
  suspend "checked_init"
QED

Resume range_frag_prefix_from_cons[literal]:
  rangeForDriverLib.range_literal_code_tac >>
  `n1 <= n2 /\ n = Num (n2 - n1)` by
    (qpat_assum `supported_iterator _ _ _ _` mp_tac >>
     qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[NoAsms, supportedStmtsTheory.supported_iterator_def]) >>
  `well_typed_literal typ (IntL n1)` by
    (qpat_assum `well_typed_expr env e1` mp_tac >>
     qpat_assum `expr_type e1 = typ` mp_tac >>
     qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     simp[NoAsms, vyperTypeSystemTheory.well_typed_expr_def, expr_type_def]) >>
  `well_typed_literal typ (IntL n2)` by
    (qpat_assum `well_typed_expr env e2` mp_tac >>
     qpat_assum `expr_type e2 = typ` mp_tac >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[NoAsms, vyperTypeSystemTheory.well_typed_expr_def, expr_type_def]) >>
  `value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2)` by
    (let fun typed lit = irule (REWRITE_RULE [vyperValueOperationTheory.evaluate_literal_def]
           (Q.INST [`lit` |-> lit] vyperTypeValuesTheory.well_typed_literal_sound)) >>
           qexistsl [`get_tenv cx`,`typ`] >> rpt conj_tac >> first_assum ACCEPT_TAC
     in conj_tac >- typed `IntL n1` >> typed `IntL n2` end) >>
  `n < dimword (:256)` by
    (qspecl_then [`get_tenv cx`,`typ`,`tyv`,`n1`,`n2`] mp_tac range_end_words >>
     qpat_assum `n = Num (n2 - n1)` SUBST1_TAC >>
     qpat_assum `is_int_type typ` (fn intty =>
       qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv` (fn et =>
         qpat_assum `value_has_type tyv (IntV n1)` (fn v1 =>
           qpat_assum `value_has_type tyv (IntV n2)` (fn v2 =>
             qpat_assum `n1 <= n2` (fn le => simp[NoAsms,intty,et,v1,v2,le])))))) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2 ** 64` >>
     conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp[NoAsms, wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
            bitTheory.TWOEXP_MONO]]) >>
  rangeForDriverLib.range_fresh_scope_tac `es` >>
  `alloca_frame cenv es sa s0 cenv es s0` by
    (irule alloca_frame_same >> simp[NoAsms]) >>
  `st.cs_next_var <= sb0.cs_next_var` by
    (qpat_assum `st = sa` SUBST1_TAC >>
     qpat_assum `sb0.cs_next_var = _` SUBST1_TAC >> decide_tac) >>
  suspend "literal_apply"
QED

fun range_specialize_init_tac entry =
  qspecl_then
    ([`DF`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`func`,`PG`,
      `cx_tops cx`,`cx`,`st0`,`RetQ`,`cenv`,`env`,`es`,`sa`,`s0`,`G0`,`tn0`] @
      entry @ [`st`,`sb0`,`entry_lbl`,`cond_lbl`,`p`,`cv`,`ev`,
               `n`,`typ`,`tyv`,`n1`,`n2`,`sz`,`id`]) mp_tac range_full_init >>
  simp[NoAsms, LET_THM];

val range_abbrev_init_tac =
  qabbrev_tac
    `init = bind (lift_sum (get_range_limits (IntV n1) (IntV n2)))
       (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
         (return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))))`;

Resume range_frag_prefix_from_cons[literal_apply]:
  range_specialize_init_tac [`es`,`s0`,`G0`,`tn0`] >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `sz = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (disj1_tac >> rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC,
            qpat_assum `n = Num (n2 - n1)` SUBST1_TAC >> simp[NoAsms] >> NO_TAC,
            qpat_assum `st = sa` SUBST1_TAC >> first_assum ACCEPT_TAC,
            qpat_assum `p = _` SUBST1_TAC >>
            qpat_assum `cv = _` SUBST1_TAC >>
            qpat_assum `ev = _` SUBST1_TAC >>
            qpat_assum `st = sa` SUBST1_TAC >>
            simp[NoAsms, ASCIInumbersTheory.toString_inj, not_fresh_at_def]]) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        qpat_assum `st = sa` SUBST1_TAC >> first_assum ACCEPT_TAC,
        decide_tac]) >>
  disch_then (qx_choose_then `w` assume_tac) >>
  range_abbrev_init_tac >>
  `eval_iterator cx (Range e1 e2) =
     return (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))` by
    (qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[NoAsms, FUN_EQ_THM, return_def] >> gen_tac >>
     irule eval_iterator_range_lit >> first_assum ACCEPT_TAC) >>
  `eval_stmt cx (For id typ (Range e1 e2) n body) =
     bind init (eval_for cx tyv id body)` by
    (pure_once_rewrite_tac[Once evaluate_def] >>
     qpat_assum `eval_iterator cx (Range e1 e2) = _` (fn iter =>
     qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv` (fn ty =>
     qpat_assum `n1 <= n2` (fn le =>
       simp[NoAsms, iter, ty, le, LET_THM, lift_option_type_def, bind_return,
         ignore_bind_def, Abbr `init`, get_range_limits_def, lift_sum_def,
         LENGTH_GENLIST, bind_assoc])))) >>
  pop_assum (fn eq =>
    qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
      (assume_tac o PURE_REWRITE_RULE [eq]) >> SUBST1_TAC eq) >>
  suspend "literal_init"
QED

(* Initialization is silent even when its bounds check fails. Its full
   outcome is used only to reach the selected machine entry. *)
fun range_prefix_init_tac source =
  let
    val run = `!ss. SND (init ss) = ss`
    val simplify = simp[NoAsms, Abbr `init`, get_range_limits_def, lift_sum_def,
      bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def] >>
      rpt (COND_CASES_TAC >> simp[NoAsms, raise_def, return_def])
  in
    sg run >- simplify >>
    `storage_trace_frame init` by
      (simp[NoAsms, Abbr `init`, storage_trace_frame_def, get_range_limits_def,
         lift_sum_def, bind_def, ignore_bind_def, check_def, assert_def, raise_def, return_def] >>
       rpt (COND_CASES_TAC >> simp[NoAsms, raise_def, return_def])) >>
    qpat_assum (`gas_outcome_full _ _ _ _ init (` @ source @ `,_,_,_) _ _`)
      (mp_then Any irule gas_prefix_full_bind_replay) >> BETA_TAC >>
    reverse (rpt conj_tac)
    >- (irule gas_prefix_full_no_outcome >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >>
       map_every qx_gen_tac [`gobs`,`res`,`ee`] >> strip_tac >>
       sg (`ee = ` @ source @ ` with gas_obs := gobs`) >-
         (qpat_assum run (qspec_then (source @ ` with gas_obs := gobs`) mp_tac) >>
          qpat_assum `init _ = (res,ee)` (fn eq => simp[NoAsms, eq])) >>
       pop_assum SUBST1_TAC >> simp[NoAsms])
    >- first_assum ACCEPT_TAC
    >- (qpat_assum run (fn eq => simp[NoAsms, eq, requests_outcomes_frame_def,
         vyperCallOutcomeFrameTheory.state_rel_frame_def]))
    >- (POP_ASSUM_LIST (K ALL_TAC) >> metis_tac [quantHeuristicsTheory.ISR_exists])
    >- simp[NoAsms, evaluate_storage_trace_frame] >>
    SIMP_TAC std_ss [sumTheory.INL_11]
  end;

fun range_init_replay_tac source =
  let
    val canonical = `storage_trace_horizon mid.storage_trace`
    val replay = `!tail. init (` @ source @ ` with gas_obs := gas_explicit _ _ ++ tail) =
                    (INL rs,mid with gas_obs := tail)`
    fun project selector fact = sg fact >-
      (qpat_assum `_ with gas_obs := _ = mid with gas_obs := []`
         (mp_tac o Q.AP_TERM selector) >> simp[NoAsms])
  in
    map_every qx_gen_tac [`marks`,`rs`,`mid`,`G`,`tn`,`t`] >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ (OK t,_,_) /\ _`
      (strip_assume_tac o PURE_REWRITE_RULE [GSYM CONJ_ASSOC] o
       SIMP_RULE pure_ss [Once IMP_CONJ_THM, Once FORALL_AND_THM]) >>
    `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
      (rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> n1 <= n2 /\ _`
      (qspec_then canonical mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
    `!ss. init ss = (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),ss)` by
      (qpat_assum `n1 <= n2` (fn le => qpat_assum `Num (n2 - n1) <= n` (fn bound =>
        simp[NoAsms, le, bound, Abbr `init`, get_range_limits_def, lift_sum_def, bind_def,
             ignore_bind_def, check_def, assert_def, vyperValueTheory.compatible_bound_def,
             return_def]))) >>
    qpat_assum replay
      (qspec_then `[]` (fn step => qpat_assum `!ss. init ss = _`
        (fn eq => strip_assume_tac
          (PURE_REWRITE_RULE [eq, pairTheory.PAIR_EQ, sumTheory.INL_11] step)))) >>
    `rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))` by
      (irule EQ_SYM >> first_assum ACCEPT_TAC) >>
    project `(\s:evaluation_state. s.scopes)` (`mid.scopes = ` @ source @ `.scopes`) >>
    project `(\s:evaluation_state. s.immutables)` (`mid.immutables = ` @ source @ `.immutables`) >>
    `body_const_cells_agree [(NONE,tops)] cx env mid` by
      (qpat_assum (`mid.immutables = ` @ source @ `.immutables`)
         (mp_then Any (irule o iffRL) body_const_cells_agree_immutables) >>
       first_assum ACCEPT_TAC)
  end;

val range_init_admissible_tac =
  qpat_assum `gas_admissible (bind init _) _ _`
    (mp_then Any mp_tac (SRULE [gasContextTheory.gas_admissible_gas_obs]
      stmtSimForRoundsTheory.gas_admissible_bind_tail)) >>
  disch_then (fn th => qpat_assum `!tail. init _ = (INL rs,mid with gas_obs := tail)`
    (mp_then Any ACCEPT_TAC th));

Resume range_frag_prefix_from_cons[literal_init]:
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `sa`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas) >>
  range_prefix_init_tac `es` >> range_init_replay_tac `es` >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def]) >>
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid` by
    range_init_admissible_tac >>
  rangeForDriverLib.range_literal_iterator_replay_tac >>
  suspend "literal_rounds"
QED

Resume range_frag_prefix_from_cons[checked_init]:
  `local_ptrs_reserved cenv st` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ret_pc_ok cenv sa t2` by
    (irule ret_pc_ok_frame >>
     qpat_assum `ret_pc_ok cenv sa s0` (irule_at Any) >>
     asm_rewrite_tac [arithmeticTheory.LESS_EQ_REFL]) >>
  `return_buf_frame d cenv st t2` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid2 t2 /\
       storage_well_formed_on cx mid2 (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `n < dimword (:256)` by
    (qpat_assum `type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env'`
       (mp_then Any mp_tac range_full_computed_bound) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2 ** 64` >>
     conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp[NoAsms, wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
            bitTheory.TWOEXP_MONO]]) >>
  `st.cs_next_var <= st.cs_next_var + 9` by decide_tac >>
  suspend "checked_apply"
QED

Resume range_frag_prefix_from_cons[checked_apply]:
  range_specialize_init_tac [`mid2`,`t2`,`G2`,`tn2`] >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_assum `sz = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (disj2_tac >> qexistsl_tac [`op1`,`op2`,`rv`,`g1`,`z1`,`g2`,`z2`] >>
          asm_rewrite_tac [] >>
          simp[NoAsms,ASCIInumbersTheory.toString_inj,not_fresh_at_def,
               DISJ_IMP_THM,FORALL_AND_THM]) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
  disch_then (qx_choose_then `w` assume_tac) >>
  range_abbrev_init_tac >>
  `bind (lift_sum (get_range_limits v1 v2))
     (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
       (eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)))) =
   bind init (eval_for cx tyv id body)` by
    (qpat_assum `v1 = IntV n1` SUBST1_TAC >> qpat_assum `v2 = IntV n2` SUBST1_TAC >>
     simp[NoAsms, Abbr `init`, ignore_bind_def, bind_assoc, bind_return]) >>
  pop_assum (fn th => mk_asm "init_bind" th >> SUBST1_TAC th) >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `st`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas_from) >>
  range_prefix_init_tac `mid2` >> range_init_replay_tac `mid2` >>
  asm "computed_eval" (fn eq =>
    qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  (let
     val tail = SRULE [gasContextTheory.gas_admissible_gas_obs]
       stmtSimForRoundsTheory.gas_admissible_bind_tail
     fun advance adm replay = qpat_assum adm (mp_then Any mp_tac tail) >>
       disch_then (fn th => qpat_assum replay
         (mp_then Any (assume_tac o BETA_RULE) th))
   in
     advance `gas_admissible (bind (bind (eval_expr cx e1) (read_result cx)) _) _ es`
       `!tail. bind (eval_expr cx e1) (read_result cx) _ = (INL v1,mid1 with gas_obs := tail)` >>
     advance `gas_admissible (bind (bind (eval_expr cx e2) (read_result cx)) _) _ mid1`
       `!tail. bind (eval_expr cx e2) (read_result cx) _ = (INL v2,mid2 with gas_obs := tail)`
   end) >>
  asm "init_bind" (fn eq =>
    qpat_assum `gas_admissible (bind (lift_sum (get_range_limits v1 v2)) _) _ mid2`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid` by
    range_init_admissible_tac >>
  rangeForDriverLib.range_computed_iterator_replay_tac >>
  suspend "computed_rounds"
QED

val range_round_guards_tac =
  rangeForDriverLib.range_join_rounds_source_tac
    `body_for_full_ok cx tyv id body rs`
    `!tenv s'' tyv t s'3' vs t' s'4' x t''. _ ==> body_for_full_ok _ _ _ _ _` >>
  rangeForDriverLib.range_join_rounds_source_tac
    `body_for_prefix_ok cx tyv id body rs`
    `!tenv s'' tyv t s'3' vs t' s'4' x t''. _ ==> body_for_prefix_ok _ _ _ _ _`;

val range_round_geometry_tac =
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC,
    qpat_assum `rs = GENLIST _ _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC];

val range_round_cons_tac =
  map_every qx_gen_tac [`a`,`rest`,`ee`,`sr`,`Gr`,`tnr`] >> strip_tac >> conj_tac
  >- (asm "round_cons"
        (qspecl_then [`st0`,`es`,`s0`,`G0`,`tn0`,`n1`,`n2`,`Num (n2-n1)`,`w`] mp_tac) >>
      impl_tac >- range_round_geometry_tac >>
      disch_then (qspecl_then [`cenv`,`Inv`,`Done`,`R`] mp_tac) >>
      impl_tac
      >- (simp[NoAsms,Abbr `Inv`,Abbr `Done`,Abbr `R`,FUN_EQ_THM] >>
          POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
          metis_tac[haltExitProjTheory.halt_exit_INR_type]) >>
      disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "round_prefix"
    (qspecl_then [`st0`,`es`,`s0`,`G0`,`tn0`,`n1`,`n2`,`Num (n2-n1)`,`w`,`Inv`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC,
        qpat_assum `rs = GENLIST _ _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC,
        simp[NoAsms,Abbr `Inv`] >> NO_TAC]) >>
  disch_then irule >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qexists `rest` >> rpt conj_tac >> first_assum ACCEPT_TAC];

val range_round_apply_tac =
  irule eval_for_rounds_prefix >>
  conj_tac
  >- (qexists `\rs b. if b then return () else eval_for cx tyv id body rs` >>
      simp[NoAsms]) >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> n1 <= n2 /\ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`Done`,`Inv`,`R`,`stmt_res_ok lctx`,
    `\a. do v <- read_result cx a; push_scope_with_var id tyv v;
             finally (try (do eval_stmts cx body; return F od) handle_loop_exception) pop_scope od`,
    `cx_tops cx`] >> BETA_TAC >>
  conj_tac >- range_round_cons_tac >>
  simp[NoAsms] >> reverse conj_tac >- first_assum ACCEPT_TAC;

val range_round_entry_tac =
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> n1 <= n2 /\ _`
    (drule_then strip_assume_tac) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_then (Pos hd) mp_tac
       bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac []) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `mid.scopes = _` SUBST1_TAC >>
     FIRST [REFL_TAC, asm_rewrite_tac []]) >>
  rangeForDriverLib.range_join_rounds_sep_tac >>
  simp[NoAsms, Abbr `Inv`, arithmeticTheory.ADD_COMM] >>
  qexists `k` >>
  `ainst.inst_id = st.cs_next_id` by
    (qpat_assum `ainst = mk_inst _ _ _ _`
      (fn th => simp[NoAsms,th,venomInstTheory.mk_inst_def])) >>
  qpat_assum `p = STRING _ _` SUBST1_TAC >>
  qpat_assum `ainst.inst_id = st.cs_next_id` SUBST1_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC;

val range_round_join_tac =
  range_round_guards_tac >> rangeForDriverLib.range_join_rounds_invariants_tac >>
  range_round_apply_tac >> range_round_entry_tac;

Resume range_frag_prefix_from_cons[literal_rounds]:
  range_round_join_tac
QED

Resume range_frag_prefix_from_cons[computed_rounds]:
  range_round_join_tac
QED

Finalise range_frag_prefix_from_cons
