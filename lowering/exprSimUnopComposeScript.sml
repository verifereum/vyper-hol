(* Ordinary unary expression simulation composition. *)
Theory exprSimUnopCompose
Ancestors
  exprUnopSimDefs exprSimUnopProps exprSimUnopComposeProps gasContext
  gasSummary gasOutcome gasSummaryCompose gasExemptCert gasNormalPrefix
  gasStorage vyperStorageTrace vyperStorageFootprint
  fragGasMode fragGasPath
  exprSimProps
  exprSimDefs
  loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt  freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps arithmeticProps vyperArith
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping vyperTypeSystem
Libs
  intLib pairLib


Theorem compile_unop_sim:
  !ctx func cenv cx ty ann bi e1 ty1 f es.
    bi <> Len /\ ~precompile_builtin bi /\ builtin_args_length_ok bi 1 /\
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (Builtin ann bi [e1]) sa = (op, sb) ==>
       ?x s1. lower_value compile_expr cenv ty1 e1 sa = (x, s1) /\
              f x s1 = (op, sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv ty1 e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx ty1 e1 es /\
    (!gs1 v1 es1. (do r <- eval_expr cx e1; read_result cx r od)
        (es with gas_obs := gs1) = (INL v1, es1) ==>
       ?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
             unop_frag ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
               (unop_result cx ann bi [expr_type e1] v1 es1) es1) ==>
    expr_sim ctx func cenv cx ty (Builtin ann bi [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty (Builtin _ _ _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty1 e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x sa sb op. f _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`ann`,`bi`] >> simp[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `!v. storage_trace_frame
         (\es. (unop_result cx ann bi [expr_type e1] v es, es))` by
    simp[storage_trace_frame_def, unop_result_def] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >> fs[]
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
          `expr_res_ok (unop_result cx ann bi [expr_type e1] v es_end)` by
            (qpat_x_assum `gas_admissible (bind (eval_expr cx (Builtin _ _ _)) _) _ es`
               (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
             disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
             asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
             simp[bind_def, unop_result_gas_obs] >>
             disch_then irule >> simp[]) >>
          fs[unop_result_gas_obs] >>
          drule_all (SIMP_RULE bool_ss [PULL_EXISTS] unop_continuation_summary) >>
          simp[unop_result_gas_obs] >>
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
  irule unop_exempt_cert >> simp[]
QED
