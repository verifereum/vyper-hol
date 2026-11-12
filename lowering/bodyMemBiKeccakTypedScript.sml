(* Full counted operand outcome followed by the memory-safe keccak suffix. *)
Theory bodyMemBiKeccakTyped
Ancestors
  bodyMemBiKeccakOpenFree bodyMemBiKeccakCompose exprSimHash exprSimMemDefs bodyMemoryPreds exprSimMemoryStack exprSimSource
  exprSimUnwrap exprSimUnopComposeProps exprSimUnopProps exprUnopSimDefs exprSimWordArgs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasNormalPrefix fragGasMode fragGasPath
  exprSimProps exprSimDefs exprSimHypsDefs loweringPosts exprLoweringProps
  exprLowering emitHelper compileEnv fragExec freshWrites
  vyperTyping vyperTypeSystem vyperValue vyperInterpreter vyperState vyperAST vyperContext
  list rich_list words vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
Libs
  pairLib

Theorem compile_keccak256_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Keccak256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  gvs[] >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once lower_value_def, compile_hash_singleton, comp_bind_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT bty) e sa` >>
  rename1 `lower_value compile_expr cenv (BaseT bty) e sa = (x,sm)` >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ code` >>
  Cases_on `code` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sb func` >>
  `cs_appends (\st. if is_bytestring_type (BaseT bty) then compile_keccak256_bytes x st
    else case BaseT bty of BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m st
      | _ => compile_keccak256_word x st)` by
    (Cases_on `bty` >> gvs[is_bytes_or_string_type_def, is_bytestring_type_def]
     >~ [`expr_type e = BaseT (BytesT bd)`] >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
                         metis_tac[hash_suffix_appends]) >>
     metis_tac[hash_suffix_appends]) >>
  qmatch_asmsub_abbrev_tac `cs_appends suffix` >>
  `suffix sm = (op,sb)` by simp[Abbr `suffix`] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `Keccak256`] >>
     simp[builtin_args_length_ok_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "normal_or_exception" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule unop_exempt_cert >> simp[builtin_args_length_ok_def]
QED

Resume compile_keccak256_sim_mem[normal_or_exception]:
  qexists_tac `marks` >> disj1_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_unop_action_general, builtin_args_length_ok_def, precompile_builtin_def] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac
  >- (gvs[] >>
      `bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         (INL v, es_end with gas_obs := [])` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
           (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
         strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
      `expr_body_pre cenv cx env e es` by
        (irule expr_body_pre_builtin_arg >>
         conj_tac >- gvs[expr_body_pre_def] >>
         qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `[e]`, `Keccak256`, `es`] >>
         gvs[expr_body_pre_def]) >>
      `expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
      drule_at (Pos (el 2)) (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
      disch_then drule >> strip_tac >>
      drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[] >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
           env_context_consistent_def] >>
      `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
       value_has_type (BaseTV bty) v` by
        (gvs[expr_result_typed_def, expr_runtime_typed_def,
             value_result_typed_def, evaluate_type_def] >>
         Cases_on `bty` >> gvs[AllCaseEqs()] >>
         Cases_on `b` >> gvs[AllCaseEqs()]) >>
      `~t.vs_halted` by
        metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
      fs[Abbr `suffix`] >>
      drule_at (Pos hd) keccak_typed_suffix_counted_open_free >>
      simp[] >> strip_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INL r`, `es_end`, `OK t'`] >>
      conj_tac
      >- (asm_simp_tac (srw_ss()) [eval_expr_unop_action_general, builtin_args_length_ok_def, precompile_builtin_def] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                    |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
          irule (SRULE [] (Q.INST [`n` |-> `0`] gas_marked_exec_no_source_read)) >>
          simp[gas_marked_path_def] >>
          gvs[unop_result_def, builtin_result_def, AllCaseEqs()]) >>
      simp[] >>
      irule expr_post_of_vv_post_stack >> goal_assum (drule_at Any)) >>
  Cases_on `res` >- gvs[] >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INR y`, `es_end`, `r`] >>
  simp[] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  gvs[]
QED

Finalise compile_keccak256_sim_mem
