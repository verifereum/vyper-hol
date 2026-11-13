(* Source-action boundaries for counted TypeBuiltin conversion composition. *)
Theory bodyMemTbConvertCompose
Ancestors
  bodyUnopFragMemory exprSimConvert gasExemptCert gasSummary gasOutcome
  gasStorage vyperStorageTrace vyperStorageFootprint
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
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  alloca_history func t0 /\ s0.vs_alloca_next <= t0.vs_alloca_next /\
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
    (\res fin tf. !H. valid_horizon cx st0 H fin.storage_trace ==>
      ?v. res = INL v /\
      expr_post H ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0 fin v op tf /\
      tf.vs_current_bb = sb.cs_current_bb /\
      tf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func tf /\ s0.vs_alloca_next <= tf.vs_alloca_next)
    (\res fin r. !H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_exit res r)
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) t0 /\
     storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then strip_assume_tac) >>
     gvs[expr_post_def]) >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then strip_assume_tac) >>
     gvs[expr_post_def, expr_val_rel_def]) >>
  qpat_x_assum `unop_frag_mem _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_mem_def]) >>
  disch_then (qspecl_then [`st0`,`s1`,`sb`,`x`,`op`,`t0`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists_tac `H` >> simp[])) >> strip_tac
  >- (`s0.vs_alloca_next <= s.vs_alloca_next` by decide_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`convert_result cx (expr_type e1) t v1`,`ee`,`r`] >>
      conj_tac
      >- (simp[gas_marked_exec_def] >> metis_tac[]) >>
      gvs[] >> disj1_tac >> rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
        (drule_then strip_assume_tac) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (drule_then strip_assume_tac) >>
      irule expr_post_convert >> simp[] >>
      qexistsl_tac [`s1`,`t0`,`v1`,`x`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) t v1`,`ee`,`r`] >>
  simp[gas_marked_exec_def]
QED


Theorem compile_convert_frag_sim_mem:
  !ctx func cenv cx ty ann t e1 f es.
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa = (op, sb) ==>
       ?x s1. lower_value compile_expr cenv (expr_type e1) e1 sa = (x, s1) /\
              f x s1 = (op, sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do r <- eval_expr cx e1; read_result cx r od)
        (es with gas_obs := gs1) = (INL v1, es1) ==>
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
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> qexistsl_tac [`ann`,`t`] >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `!v. storage_trace_frame
         (\es. (convert_result cx (expr_type e1) t v, es))` by
    simp[storage_trace_frame_def] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_convert_action] >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           asm_simp_tac (srw_ss()) [eval_expr_convert_action] >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_convert_action] >> fs[]
      >- (qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
            (drule_then strip_assume_tac) >>
          gvs[] >>
          `!H. valid_horizon cx st0 H es_end.storage_trace ==>
               expr_post H ctx func cenv cx e1 es sa s1 s0
                 (es_end with gas_obs := []) v x t` by
            (rpt strip_tac >> first_x_assum drule >> simp[]) >>
          `?H. valid_horizon cx st0 H es_end.storage_trace` by metis_tac[] >>
          `bind (eval_expr cx e1) (read_result cx)
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          qpat_x_assum `!gs1 v1 es1. _`
            (drule o CONV_RULE (DEPTH_CONV ETA_CONV)) >> strip_tac >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `expr_res_ok (convert_result cx (expr_type e1) t v)` by
            (qpat_x_assum `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
               (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
             disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
             asm_simp_tac (srw_ss()) [eval_expr_convert_action] >>
             simp[bind_def] >>
             disch_then irule >> simp[]) >>
          drule_all (SIMP_RULE bool_ss [PULL_EXISTS] convert_continuation_summary_mem) >>
          rewrite_tac[gas_summary_at_def] >> strip_tac >>
          qexistsl_tac [`res`,`es_end'`,`r`] >>
          (conj_tac
           >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                      |> REWRITE_RULE [APPEND_NIL]) >>
               qexistsl_tac [`es_end`,`t`,`v`] >> gvs[]) >>
           gvs[] >> disj2_tac >> first_assum ACCEPT_TAC)) >>
      Cases_on `res`
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
            (drule_then mp_tac) >> simp[]) >>
      simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
      simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      gvs[] >> disj2_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule convert_exempt_cert >> simp[]
QED

(* Reading a result and converting it adds nothing to the storage trace. *)
Theorem convert_read_continuation_frame:
  storage_trace_frame
    (bind (read_result cx tv) (\v es. (convert_result cx t dst v,es)))
Proof
  irule storage_trace_frame_bind >> simp[storage_trace_frame_read_result] >>
  rpt strip_tac >> simp[storage_trace_frame_def]
QED
