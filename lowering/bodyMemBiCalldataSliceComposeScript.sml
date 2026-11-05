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

Theorem calldata_slice_continuation_summary_mem:
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
  expr_post ctx func cenv cx e es sa sm s0 ee v x s /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_res_ok (builtin_result cx ee.accounts (BaseT (BytesT (Dynamic n)))
    (CalldataSlice n) [expr_type e] [v]) ==>
  ?marks. gas_summary_at T (ctx,func) marks
    (\st. ((case builtin_result cx st.accounts (BaseT (BytesT (Dynamic n)))
      (CalldataSlice n) [expr_type e] [v] of
        INL rv => INL (Value rv) | INR exc => INR exc),st)) (ee,s)
    (\res fin t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
        es sa sb s0 fin tv vv t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic n)))
        (lowered_value_type cenv
          (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
        fin tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
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
  `stmt_state_rel ctx func cenv cx ee s` by metis_tac[expr_post_state] >>
  `eval_operand x s = SOME (n2w a)` by
    (drule expr_post_word_operand >>
     simp[evaluate_type_def, is_word_type_def, word_value_def, val_to_w256_def,
          integer_wordTheory.i2w_pos]) >>
  `wb_frame cenv es sa s0 s` by metis_tac[expr_post_frame] >>
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
       vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
        ee sm r s ee (Value rv)
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)) u /\
       vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
        ee (Value rv)
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)) u) /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
      u.vs_current_bb = r.cs_current_bb /\
      u.vs_inst_idx = LENGTH r.cs_current_insts) \/
     (exit_result out /\ expr_exit
      (case evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n of
        INL v => INL v | INR err => INR (Error err)) out))` by
    (irule (slice_calldata_path_mem |> SPEC_ALL
       |> Q.INST [`e` |-> `Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]`]
       |> SRULE [expr_type_def]) >>
     simp[mk_ptr_def, calldata_slice_memory_bytes] >>
     fs[calldata_slice_memory_bytes] >>
     qexists_tac `x` >> simp[])
  >- suspend "success" >>
  suspend "abort"
QED

Resume calldata_slice_continuation_summary_mem[success]:
  `vv_post ctx func cenv cx
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
    es sa r s0 ee (Value rv)
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)) u` by
      (irule vv_post_prefix_frame >> simp[] >>
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
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "normal" >>
  suspend "exempt"
QED

Resume compile_calldata_slice_vv_sim_mem[normal]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac
  >- suspend "success" >>
  suspend "exception"
QED

Resume compile_calldata_slice_vv_sim_mem[success]:
  gvs[] >>
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
  `as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
    (compile_slice_calldata x (Lit (n2w n))
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm) =
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory),r)` by
    simp[as_ptr_val_def] >>
  drule_at (Pat `expr_post`) calldata_slice_continuation_summary_mem >>
  disch_then (qspecl_then
    [`LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr q LocMemory)`,
     `r`, `n`, `gas_explicit marks s0.vs_gas_readings`, `env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[eval_expr_unary_builtin_action, builtin_args_length_ok_def,
       expr_type_def] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac >>
  rename1 `gas_marked_exec _ _ _ _ marks' res fin out` >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`res`, `fin`, `out`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >> metis_tac[]) >>
  gvs[expr_type_def] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[]
QED

Resume compile_calldata_slice_vv_sim_mem[exception]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  simp[eval_expr_unary_builtin_action, builtin_args_length_ok_def,
       gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r'`] >> simp[] >>
  conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  Cases_on `r'` >> Cases_on `y` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >>
  Cases_on `err` >> gvs[expr_exit_def]
QED

Resume compile_calldata_slice_vv_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[eval_expr_unary_builtin_action, builtin_args_length_ok_def] >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind a k) _` >>
  `ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x'` >> Cases_on `q'` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_value >> simp[Abbr `a`]
QED

Finalise compile_calldata_slice_vv_sim_mem
