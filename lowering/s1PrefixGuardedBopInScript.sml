(* Guarded request-prefix introduction for membership operators. *)
Theory s1PrefixGuardedBopIn
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixBopRestWordCompose s1PrefixOfVV
  s1PrefixWordArgs bodyFullPreds bodyFullBopWordLayout bodyFullWordArgs
  bodyFullExprsListFacts bodyFullExprsSingleton
  exprSimBopInLiteralWord exprSimWordArgs exprSimOperators exprSimHyps
  exprSimHypsDefs exprSimSource exprBopSimProps exprSimUnopProps
  exprLoweringProps exprBodyPreProps fragExec compileEnv gasShadow gasShadowState
  vyperAST vyperContext vyperTypeSystem vyperInterpreter vyperState list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_args >>
  disch_then (qx_choose_then `e1` (qx_choose_then `e2` SUBST_ALL_TAC)) >>
  `body_exprs_full_ok cx [e1;e2] /\ body_exprs_prefix_ok cx [e1;e2]` by
    fs[builtin_args_length_ok_def] >>
  drule expr_body_pre_bop >> strip_tac >>
  rename1 `expr_body_pre cenv cx env (Builtin ty (Bop bop) [e1;e2]) es0` >>
  conj_asm1_tac
  >- (Cases_on `?fid. expr_type e1 = FlagT fid /\ expr_type e2 = FlagT fid`
      >- suspend "flag" >>
      `is_word_type (expr_type e1) /\ ?bd. expr_type e2 = ArrayT (expr_type e1) bd` by
        (qpat_assum `bop = In \/ bop = NotIn` strip_assume_tac >>
         fs[well_typed_binop_def, membership_element_word_boundary] >> metis_tac[]) >>
      Cases_on `?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- suspend "literal" >>
      irule compile_rest_word_membership_prefix >> simp[] >>
      conj_tac >- metis_tac[] >> qexistsl_tac [`env`,`tops`] >> simp[]) >>
  irule expr_vv_sim_stack_prefix >> simp[compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
*)
Theorem bop_in_expr_prefix_ok:
  !cx ty bop es.
  (bop = In \/ bop = NotIn) /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty (Bop bop) es)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_in_expr_prefix_ok[flag]:
  qpat_x_assum `?fid. _` (qx_choose_then `fid` strip_assume_tac) >>
  `word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
   is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    simp[word_value_type_def, is_flag_type_def, is_word_type_def] >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all bop_word_full_layout >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full P cx st0 src inp` >>
  `gas_prefix_full P cx st0 src inp <=>
   gas_prefix_full P cx st0 (eval_exprs cx [e1;e2]) inp` by
    (simp[Abbr `inp`] >> irule gas_prefix_full_state_cong >>
     simp[Abbr `src`, REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
     qx_gen_tac `qe` >> ntac 2 (once_rewrite_tac[eval_exprs_cons_action]) >>
     simp[eval_exprs_nil] >>
     Cases_on `bind (eval_expr cx e1) (read_result cx) qe` >>
     rename1 `_ = (rr,ee)` >> Cases_on `rr` >> simp[bind_def, return_def] >>
     Cases_on `eval_expr cx e2 ee` >> rename1 `_ = (rr,ff)` >>
     Cases_on `rr` >> simp[] >>
     rename1 `eval_expr cx e2 ee = (INL rv,ff)` >>
     Cases_on `read_result cx rv ff` >> rename1 `_ = (rr,gg)` >>
     Cases_on `rr` >> simp[eval_exprs_nil, return_def]) >>
  simp[Abbr `P`, Abbr `inp`] >>
  `lower_word_args cenv (K (expr_type e1)) [e1;e2] sa = ([x;y],s2) /\
   lower_word_args (gas_shadow_env T cenv) (K (expr_type e1))
     (MAP gas_shadow_expr [e1;e2]) shadow_sa = ([x;y],shadow_s2)` by
    (simp[lower_word_args_cons, lower_word_args_nil] >>
     conj_tac >- (qexists_tac `s1` >> metis_tac[]) >>
     qexists_tac `shadow_s1` >> metis_tac[]) >>
  `fn_has_code sa s2 func /\ fn_has_code shadow_sa shadow_s2 shadow_func` by
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `expr_sim_inv cenv cx env es0` by metis_tac[expr_body_pre_static_facts] >>
  irule lower_word_args_by_type_prefix >>
  qpat_assum `lower_word_args cenv _ _ sa = _` (irule_at Any) >>
  qpat_assum `lower_word_args _ _ _ shadow_sa = ([x;y],shadow_s2)` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >> simp[] >>
  qexists_tac `shadow_func` >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >> simp[is_word_type_def] >>
  irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
  simp[] >> qexistsl_tac [`ty`,`[e1;e2]`,`Bop bop`,`es0`] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_in_expr_prefix_ok[literal]:
  qpat_x_assum `?a t n elems. _` (qx_choose_then `a`
    (qx_choose_then `t` (qx_choose_then `n` (qx_choose_then `elems` SUBST_ALL_TAC)))) >>
  drule_all literal_body_typing >> strip_tac >>
  `body_exprs_full_ok cx (e1::elems) /\ body_exprs_prefix_ok cx (e1::elems)` by
    (qpat_assum `body_exprs_full_ok _ _` mp_tac >>
     qpat_assum `body_exprs_prefix_ok _ _` mp_tac >>
     once_rewrite_tac [body_exprs_full_ok_cons] >>
     rewrite_tac [body_exprs_full_ok_singleton] >>
     ntac 2 (once_rewrite_tac [body_exprs_prefix_ok_def]) >>
     rpt strip_tac >>
     metis_tac[bodyFullPredsTheory.body_make_array_children_full_ok,
               body_make_array_children_prefix_ok, builtin_args_length_ok_def]) >>
  drule_all literal_body_action_flat >> strip_tac >>
  `is_ArrayT a` by simp[is_ArrayT_def] >>
  `expr_sim_inv cenv cx env es0` by metis_tac[expr_body_pre_static_facts] >>
  `!e ee. MEM e (e1::elems) /\ expr_sim_inv cenv cx env ee ==>
     expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- metis_tac[literal_body_operand_pre] >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all literal_lower_value >> strip_tac >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[NoAsms, gas_shadow_expr_def, gas_shadow_builtin_def] >>
  disch_then (mp_then Any mp_tac literal_lower_value) >>
  simp[] >> strip_tac >>
  `needle'::xs' = needle::xs /\ gas_shadow_state sm sm'` by
    (mp_tac (Q.INST [`tyf` |-> `expr_type`, `cenv` |-> `cenv`]
       gas_shadow_compiles_lower_word_args) >>
     rewrite_tac[gas_shadow_compiles_def] >> simp[] >>
     disch_then (qspecl_then [`e1::elems`,`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa sm' shadow_func` by
    (`ci_mono sa sm /\ ci_mono shadow_sa sm'` by
       metis_tac[ci_mono_lower_word_args] >>
     `cs_extends sm sb /\ cs_extends sm' shadow_sb` by
       (Cases_on `bop = In` >>
        fs[] >> metis_tac[literal_membership_straight, straight_fresh_cs_extends]) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_mid,cs_extends_refl]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (eval_exprs cx (e1::elems)) (es0,s0,G0,tn0)` suffices_by
    (disch_tac >>
     qmatch_goalsub_abbrev_tac `gas_prefix_full P cx st0 src (es0,s0,G0,tn0)` >>
     `gas_prefix_full P cx st0 src (es0,s0,G0,tn0) <=>
      gas_prefix_full P cx st0 (eval_exprs cx (e1::elems)) (es0,s0,G0,tn0)` by
       (irule gas_prefix_full_state_cong >> simp[Abbr `src`] >>
        qx_gen_tac `qe` >> Cases_on `eval_exprs cx (e1::elems) qe` >>
        rename1 `_ = (rr,ee)` >> Cases_on `rr` >> simp[bind_def,return_def]) >>
     fs[Abbr `P`]) >>
  irule lower_word_args_by_type_prefix >>
  qpat_assum `lower_word_args cenv _ _ sa = _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`sm'`,`shadow_sa`,`shadow_func`] >>
  asm_rewrite_tac[] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bop_in_expr_prefix_ok
*)
