(* Counted composition of the operand and the allocating slice suffix. *)
Theory bodyMemBiCalldataSliceCompose
Ancestors
  bodyMemBiCalldataSliceFacts bodyMemBiCalldataSlicePath
  exprSimCalldataSlice exprSimHash exprSimSource exprSimMemDefs
  exprSimProps exprSimDefs loweringPosts exprSimHypsDefs
  gasSummary fragGasMode gasOutcome gasNormalPrefix
  exprLoweringProps exprLowering compileEnv context builtinBytes
  vyperAST vyperState vyperInterpreter vyperValue vyperTypeSystem
  vyperContext vyperTyping vyperValueOperation
  venomState words list finite_map arithmetic
  exprSimWordArgs valueEncoding loweringSlice vyperEvalExprPreservesScopesDom
  rich_list fragExec fragGasPath gasContext gasSummaryCompose gasExemptCert
  gasStorage vyperStorageTrace vyperStorageFootprint

Theorem calldata_slice_continuation_summary_mem:
  !ctx func cenv cx env n es e sa x sm vv sb s0 gs v ee s st0.
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es /\
  expr_type e = BaseT (UintT 256) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
    (compile_slice_calldata x (Lit (n2w n))
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  ee.gas_obs = [] /\ value_has_type (BaseTV (UintT 256)) v /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sm s0 ee v x s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0) /\
  alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_res_ok (builtin_result cx ee.accounts (BaseT (BytesT (Dynamic n)))
    (CalldataSlice n) [expr_type e] [v]) ==>
  ?marks. gas_summary_at T (ctx,func) marks
    (\st. ((case builtin_result cx st.accounts (BaseT (BytesT (Dynamic n)))
      (CalldataSlice n) [expr_type e] [v] of
        INL rv => INL (Value rv) | INR exc => INR exc),st)) (ee,s)
    (\res fin t. !H. valid_horizon cx st0 H fin.storage_trace ==>
      ?tv. res = INL tv /\
      vv_post H ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
        es sa sb s0 fin tv vv t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic n)))
        (lowered_value_type cenv
          (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
        fin tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res fin r. !H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  Cases_on `compile_slice_calldata x (Lit (n2w n))
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  `?a. v = IntV (&a) /\ a < 2 ** 256` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     `?m. i = &m` by (qexists_tac `Num i` >> intLib.COOPER_TAC) >> gvs[]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s` by
    metis_tac[expr_post_state] >>
  `eval_operand x s = SOME (n2w a)` by
    (drule expr_post_word_operand >>
     simp[evaluate_type_def, is_word_type_def, word_value_def, val_to_w256_def,
          integer_wordTheory.i2w_pos]) >>
  `wb_frame cenv es ee sa s0 s` by metis_tac[expr_post_frame] >>
  `~expr_has_effect (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) ==>
   pure_frame cenv func es sa s0 s` by
    (simp[expr_has_effect_thm] >> metis_tac[expr_post_pure_frame]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `well_typed_expr env
     (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])` by
    fs[expr_body_pre_def] >>
  `0 < n /\ n < 2 ** 256` by
    (drule calldata_slice_typing >> simp[]) >>
  `32 + 32 * word_size n < 2 ** 64` by
    metis_tac[calldata_slice_allocation_limit] >>
  `context_well_typed cx` by fs[expr_body_pre_def, expr_sim_inv_def] >>
  `?m out. gas_marked_path T ctx func s m out /\
    ((?u. out = OK u /\
      (?rv. (case evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n of
        INL v => INL v | INR err => INR (Error err)) = INL rv /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         vv_post H ctx func cenv cx
          (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
          ee sm r s ee (Value rv)
          (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)) u) /\
       vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
        ee (Value rv)
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)) u) /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
      u.vs_current_bb = r.cs_current_bb /\
      u.vs_inst_idx = LENGTH r.cs_current_insts) \/
     (exit_result out /\ expr_exit
      (case evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n of
        INL v => INL v | INR err => INR (Error err)) out))` by
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`,
       `Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]`, `ee`,
       `sm`, `r`, `x`, `mk_ptr q LocMemory`, `n`, `a`, `s`,
       `case evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n of
          INL v => INL v | INR err => INR (Error err)`, `st0`,
       `ee.storage_trace`] mp_tac slice_calldata_path_mem >>
     impl_tac
     >- (simp[mk_ptr_def, expr_type_def, type_memory_bytes_def] >>
         fs[type_memory_bytes_def, expr_type_def, mk_ptr_def] >>
         conj_tac >- metis_tac[] >> simp[]) >>
     simp[])
  >- suspend "success" >>
  suspend "abort"
QED

Resume calldata_slice_continuation_summary_mem[success]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
    es sa r s0 ee (Value rv)
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)) u` by
      (rpt strip_tac >> irule vv_post_prefix_frame >> simp[] >>
       qexistsl_tac [`ee`, `sm`, `s`] >> simp[]) >>
  qexists_tac `REPLICATE m F` >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value rv)`, `ee`, `OK u`] >>
  simp[gas_marked_exec_def, gas_explicit_replicate_false] >>
  `ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  simp[calldata_slice_lowered_value_type] >>
  fs[builtin_result_def, evaluate_builtin_def]
QED

Resume calldata_slice_continuation_summary_mem[abort]:
  qexists_tac `REPLICATE m F` >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`case builtin_result cx ee.accounts (BaseT (BytesT (Dynamic n)))
    (CalldataSlice n) [BaseT (UintT 256)] [IntV (&a)] of
      INL rv => INL (Value rv) | INR exc => INR exc`, `ee`, `out`] >>
  simp[gas_marked_exec_def] >>
  disj2_tac >> simp[] >>
  fs[builtin_result_def, evaluate_builtin_def] >>
  Cases_on `evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n` >>
  fs[expr_exit_def] >>
  Cases_on `out` >> Cases_on `y` >> fs[expr_exit_def]
QED

Finalise calldata_slice_continuation_summary_mem

Theorem compile_calldata_slice_vv_sim_mem:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es /\
  expr_type e = BaseT (UintT 256) /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es
Proof
  strip_tac >> simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_calldata_slice_parts] >>
  Cases_on `lower_value compile_expr cenv (BaseT (UintT 256)) e sa` >>
  simp[] >> strip_tac >>
  rename1 `lower_value compile_expr cenv _ e sa = (x,sm)` >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     fs[expr_body_pre_def]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  Cases_on `compile_slice_calldata x (Lit (n2w n))
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  drule slice_calldata_shape >> strip_tac >>
  `cs_extends sm r` by
    fs[cs_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `x`, `s0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  `eval_expr cx (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. ((case builtin_result cx es.accounts (BaseT (BytesT (Dynamic n)))
                  (CalldataSlice n) [expr_type e] [v] of
                  INL w => INL (Value w) | INR exc => INR exc), es))` by
    simp[eval_expr_unary_builtin_action, precompile_builtin_def,
         builtin_args_length_ok_def] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- suspend "normal" >>
  strip_tac >> suspend "exempt"
QED

Resume compile_calldata_slice_vv_sim_mem[normal]:
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `es_end`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      conj_tac
      >- (irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
  `?H1. valid_horizon cx st0 H1 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE))
  >- suspend "success" >>
  suspend "exception"
QED

Resume compile_calldata_slice_vv_sim_mem[success]:
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (drule_then (qx_choose_then `v` strip_assume_tac)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sm s0 (es_end with gas_obs := []) v x t`
    by (rpt strip_tac >>
        qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?v'. _`
          (drule_then strip_assume_tac) >> gvs[]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  `value_has_type (BaseTV (UintT 256)) v` by
    metis_tac[expr_body_pre_base_result] >>
  `expr_res_ok (builtin_result cx es_end.accounts (BaseT (BytesT (Dynamic n)))
    (CalldataSlice n) [expr_type e] [v])` by
    (qpat_x_assum `gas_admissible (eval_expr cx (Builtin _ _ _)) _ es`
      (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[eval_expr_unary_builtin_action, precompile_builtin_def,
          builtin_args_length_ok_def, bind_def] >>
     Cases_on `builtin_result cx es_end.accounts (BaseT (BytesT (Dynamic n)))
       (CalldataSlice n) [BaseT (UintT 256)] [v]` >>
     simp[expr_vv_res_ok_def, expr_res_ok_def]) >>
  `!H. valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (irule vyperStorageFootprintTheory.valid_horizon_frame >>
        qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`, `INL v`,
          `es_end with gas_obs := []`,
          `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
        asm_simp_tac (srw_ss()) []) >>
     metis_tac[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `n`, `es`, `e`, `sa`, `x`,
    `sm`, `LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)`,
    `r`, `s0`, `gas_explicit marks s0.vs_gas_readings`, `v`,
    `es_end with gas_obs := []`, `t`, `st0`] mp_tac
    calldata_slice_continuation_summary_mem >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[])) >>
  strip_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  disch_then (qx_choosel_then [`res'`, `fin`, `out`]
    (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
  qexistsl_tac [`res'`, `fin`, `out`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >> metis_tac[]) >>
  disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE))
  >- (disj1_tac >> qexists_tac `t'` >> simp[expr_type_def] >> metis_tac[]) >>
  disj2_tac >> simp[] >> metis_tac[]
QED

Resume compile_calldata_slice_vv_sim_mem[exception]:
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `expr_exit res r` by metis_tac[] >>
  Cases_on `res` >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> Cases_on `r` >> Cases_on `y` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >>
  Cases_on `err` >> gvs[expr_exit_def]
QED

Resume compile_calldata_slice_vv_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind a k) _` >>
  `ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x'` >> Cases_on `q'` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_value >> simp[Abbr `a`]
QED

Finalise compile_calldata_slice_vv_sim_mem
