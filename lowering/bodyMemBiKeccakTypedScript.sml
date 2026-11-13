(* Full counted operand outcome followed by the memory-safe keccak suffix. *)
Theory bodyMemBiKeccakTyped
Ancestors
  bodyMemBiKeccakOpenFree bodyMemBiKeccakCompose exprSimHash exprSimMemDefs bodyMemoryPreds exprSimMemoryStack exprSimSource
  exprSimUnwrap exprSimUnopComposeProps exprSimUnopProps exprUnopSimDefs exprSimWordArgs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasNormalPrefix fragGasMode fragGasPath
  gasStorage vyperStorageTrace vyperStorageFootprint
  exprSimProps exprSimDefs exprSimHypsDefs loweringPosts exprLoweringProps
  exprLowering emitHelper compileEnv fragExec freshWrites
  vyperTyping vyperTypeSystem vyperValue vyperInterpreter vyperState vyperAST vyperContext
  list rich_list words vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
Libs
  pairLib

Theorem keccak_vv_post_transport[local]:
  !(H0:(bool # bytes32 # type_value) list # num list)
   (H:(bool # bytes32 # type_value) list # num list)
   ctx func cenv cx e es sa sb s0 es' tv vt op u s.
  vv_post H0 ctx func cenv cx e es sa sb s0 es' tv (StackValue vt op) u /\
  stmt_state_rel H ctx func cenv cx es' s /\ storage_well_formed_on cx es' (FST H) /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx ==>
  vv_post H ctx func cenv cx e es sa sb s0 es' tv (StackValue vt op) u
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `stmt_state_rel H ctx func cenv cx es' u` by
    metis_tac[INST_TYPE [alpha |-> ``:256``]
      exprLoweringPropsTheory.stmt_state_rel_fields_transport] >>
  rewrite_tac[vv_post_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >> gvs[vv_storage_live_def]
QED

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
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `x`, `s0`] mp_tac) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[])) >>
  `!v. storage_trace_frame
         (\es. (unop_result cx (BaseT (BytesT (Fixed 32))) Keccak256
                   [expr_type e] v es, es))` by
    simp[storage_trace_frame_def, unop_result_def] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_unop_action_general,
        builtin_args_length_ok_def, precompile_builtin_def] >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[])
  >- suspend "normal_or_exception" >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule unop_exempt_cert >> simp[builtin_args_length_ok_def]
QED

Resume compile_keccak256_sim_mem[normal_or_exception]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
   >- (qexists_tac `marks` >> disj1_tac >>
       asm_simp_tac (srw_ss()) [eval_expr_unop_action_general,
         builtin_args_length_ok_def, precompile_builtin_def] >>
       irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[] >>
       irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
       metis_tac[])) >>
  `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
     es_end.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_unop_action_general,
    builtin_args_length_ok_def, precompile_builtin_def] >>
  fs[]
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
        (drule_then strip_assume_tac) >>
      gvs[] >>
      `!H. valid_horizon cx st0 H es_end.storage_trace ==>
           expr_post H ctx func cenv cx e es sa sm s0
             (es_end with gas_obs := []) v x t` by
        (rpt strip_tac >> first_x_assum drule >> simp[]) >>
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
      qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `storage_trace_horizon es_end.storage_trace` assume_tac) >>
      drule_at (Pos hd) keccak_typed_suffix_counted_open_free >>
      simp[] >> strip_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INL r`, `es_end`, `OK t'`] >>
      conj_tac
      >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                    |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
          irule (SRULE [] (Q.INST [`n` |-> `0`] gas_marked_exec_no_source_read)) >>
          simp[gas_marked_path_def] >>
          gvs[unop_result_def, builtin_result_def, AllCaseEqs()]) >>
      disj1_tac >> qexists_tac `t'` >> simp[] >>
      rpt strip_tac >>
      rename1 `valid_horizon cx st0 H2 es_end.storage_trace` >>
      `vv_post H2 ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
         es sa sb s0 (es_end with gas_obs := []) (Value r)
         (StackValue (BaseT (BytesT (Fixed 32))) op) t'` by
        (irule keccak_vv_post_transport >>
         qexistsl_tac [`storage_trace_horizon es_end.storage_trace`, `t`] >>
         simp[] >>
         qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (qspec_then `H2` mp_tac) >>
         simp[expr_post_def]) >>
      drule expr_post_of_vv_post_stack >> simp[])
  >> Cases_on `res`
  >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
        (drule_then mp_tac) >> simp[]) >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INR y`, `es_end`, `r`] >>
  simp[] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  gvs[] >> disj2_tac >> first_assum ACCEPT_TAC
QED

Finalise compile_keccak256_sim_mem
