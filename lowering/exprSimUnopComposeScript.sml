(* Ordinary unary expression simulation composition. *)
Theory exprSimUnopCompose
Ancestors
  exprUnopSimDefs exprSimUnopProps exprSimUnopComposeProps gasContext
  gasSummary gasOutcome gasSummaryCompose gasExemptCert gasNormalPrefix
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
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >>
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
          drule_all unop_continuation_summary >>
          simp[unop_result_gas_obs] >>
          rewrite_tac[gas_summary_at_def] >> strip_tac >>
          qexistsl_tac [`res`,`es_end'`,`r`] >>
          (conj_tac
           >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                      |> REWRITE_RULE [APPEND_NIL]) >>
               qexistsl_tac [`es_end`,`t`,`v`] >> gvs[]) >>
           gvs[])) >>
      Cases_on `res` >- gvs[] >>
      simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
      simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      gvs[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule unop_exempt_cert >> simp[]
QED
