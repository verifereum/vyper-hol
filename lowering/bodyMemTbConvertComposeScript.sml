(* Source-action boundaries for counted TypeBuiltin conversion composition. *)
Theory bodyMemTbConvertCompose
Ancestors
  bodyUnopFragMemory exprSimConvert gasExemptCert gasSummary gasOutcome
  gasContext exprSimDefs loweringPosts exprSimMemDefs fragExec
  exprLoweringProps fragGasMode fragGasPath gasSummaryCompose list
  vyperInterpreter vyperState vyperValue vyperAST
Libs
  pairLib

Theorem eval_expr_convert_action:
  bind (eval_expr cx (TypeBuiltin ann Convert t [e])) (read_result cx) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. (convert_result cx (expr_type e) t v, es))
Proof
  pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
              (read_result cx) x` >>
  drule (SRULE [SF ETA_ss] eval_expr_convert_cases) >>
  strip_tac >> gvs[bind_def]
QED

Theorem convert_operand_admissible:
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
                    (read_result cx)) expr_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[eval_expr_convert_action] >>
  rw[gas_admissible_def] >>
  Cases_on `res`
  >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Theorem convert_exempt_cert:
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
                    (read_result cx)) (return ())) start marks out endpoint
Proof
  strip_tac >> rewrite_tac[eval_expr_convert_action] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  `ignore_bind
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v es. (convert_result cx (expr_type e) t v,es))) (return ()) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind (\es. (convert_result cx (expr_type e) t v,es))
       (return ()))` by
    (qmatch_goalsub_abbrev_tac `bind a _` >>
     simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[] >>
     Cases_on `convert_result cx (expr_type e) t a'` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_value >> simp[]
QED

Theorem convert_continuation_summary_mem:
  expr_post ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  alloca_history func t0 /\ s0.vs_alloca_next <= t0.vs_alloca_next /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  unop_frag_mem ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
    (convert_result cx (expr_type e1) t v1) (ee with gas_obs := []) /\
  expr_res_ok (convert_result cx (expr_type e1) t v1) /\
  f x s1 = (op,sb) /\ (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s1 /\ is_word_type ann /\
  is_word_type (expr_type e1) /\ sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at T (ctx,func) []
    (\vs. (convert_result cx (expr_type e1) t v1,vs))
    (ee with gas_obs := [],t0)
    (\res fin t'. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0
        fin v op t' /\
      t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  qpat_x_assum `unop_frag_mem _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_mem_def]) >>
  disch_then (qspecl_then [`s1`,`sb`,`x`,`op`,`t0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`convert_result cx (expr_type e1) t v1`,`ee`,`r`] >>
      conj_tac
      >- (simp[gas_marked_exec_def] >> metis_tac[]) >>
      gvs[] >> irule expr_post_convert >> simp[] >>
      qexistsl_tac [`s1`,`t0`,`v1`,`x`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) t v1`,`ee`,`r`] >>
  simp[gas_marked_exec_def]
QED

Theorem compile_convert_frag_sim_mem:
  !ctx func cenv cx ty ann t e1 f es.
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa = (op,sb) ==>
       ?x s1. lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
              f x s1 = (op,sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op,sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op,sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do r <- eval_expr cx e1; read_result cx r od)
        (es with gas_obs := gs1) = (INL v1,es1) ==>
       ?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
         unop_frag_mem ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
           (convert_result cx (expr_type e1) t v1) es1) ==>
    expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[vyperASTTheory.expr_type_def] >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty (TypeBuiltin _ _ _ _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ (expr_type e1) e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x sa sb op. f _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> qexistsl_tac [`ann`,`t`] >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_convert_action] >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >>
          `bind (eval_expr cx e1) (read_result cx)
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          qpat_x_assum `!gs1 v1 es1. _`
            (drule o CONV_RULE (DEPTH_CONV ETA_CONV)) >> strip_tac >>
          `~t'.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `expr_res_ok (convert_result cx (expr_type e1) t v)` by
            (qpat_x_assum `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
               (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
             disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
             asm_simp_tac (srw_ss()) [eval_expr_convert_action] >> simp[bind_def]) >>
          drule_all convert_continuation_summary_mem >>
          rewrite_tac[gas_summary_at_def] >> strip_tac >>
          qexistsl_tac [`res`,`es_end'`,`r`] >>
          (conj_tac
           >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                      |> REWRITE_RULE [APPEND_NIL]) >>
               qexistsl_tac [`es_end`,`t'`,`v`] >> gvs[]) >> gvs[])) >>
      Cases_on `res` >- gvs[] >>
      simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
      simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >> gvs[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule convert_exempt_cert >> simp[]
QED
