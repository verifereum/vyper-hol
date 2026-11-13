(* Ordinary environment reads under the joint full judgment. *)
Theory bodyFullBuiltinEnvReads
Ancestors
  bodyFullBuiltinEnvReadsStep
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimHypsDefs
  bodyFullGhostFrame gasOutcomeFullCompose fragGasSeqPtr
  exprSimSource exprSimProps exprLoweringProps emitHelperProps
  compileEnv exprLowering vyperTypeBuiltins vyperTypeSystem vyperContext vyperState
  vyperInterpreter vyperAST vyperValue valueEncoding words list

val _ = Parse.hide "body";

Theorem env_reads_source[local]:
  item <> PrevHash /\ item <> MsgGas ==>
  ?v. evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
      (!tail. bind (eval_expr cx (Builtin (env_item_type item) (Env item) []))
        (read_result cx) (es with gas_obs := tail) =
        (INL v, es with gas_obs := tail)) /\
      is_word_type (env_item_type item) /\
      (!tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v)
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, return_def, raise_def,
       get_accounts_def, lift_sum_def, builtin_args_length_ok_def,
       read_result_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `item` >>
  gvs[evaluate_builtin_def, env_item_type_def, is_word_type_def,
      evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
      return_def, read_result_def] >>
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []
QED

Theorem env_reads_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (?i. bt = Env i /\ i <> PrevHash /\ i <> MsgGas) /\
    builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `args = [] /\ a = env_item_type i` by
    (gvs[expr_body_pre_def, well_typed_expr_def,
         well_typed_builtin_app_def]) >>
  gvs[] >>
  conj_asm1_tac
  >- (rw[expr_sim_full_def] >>
      drule_all env_reads_source >>
      disch_then (qspecl_then [`es`, `cx`] strip_assume_tac) >>
      drule lower_value_env >> strip_tac >>
      `!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
      drule_all env_reads_step_full >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`]
        strip_assume_tac) >>
      irule gas_outcome_full_pure >> (reverse conj_tac >- simp[]) >>
      qexistsl_tac [`G'`, `es`, `INL v`, `t`, `tn'`] >>
      simp[] >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      FAIL_TAC "posts") >>
  irule expr_vv_sim_stack_full >> simp[expr_type_def] >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var i sa` >> simp[as_stack_val_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  Cases_on `i` >> gvs[env_item_type_def, is_word_type_def]
QED
