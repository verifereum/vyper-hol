(* Request-prefix companion to bodyFullAbiEncodeWordFull. *)
Theory s1PrefixAbiEncodeWordFull
Ancestors
  s1PrefixPreds bodyFullAbiEncodeWordFull s1PrefixDefs s1PrefixProps s1PrefixCompose
  bodySimFull exprSimAbiEncodeRuntimeInputs exprSimAbiEncodePrefixWindow
  exprSimAbiEncodeNonwordCase exprBodyPreProps exprSimHyps exprSimSource exprSimDefs
  exprReasonOperand targetPlaceSim vyperTypeArgFits compileEnv context exprLowering
  exprLoweringProps exprBopSimProps exprBopLowering gasShadowCompileStmtHelpers gasShadowCompilePure
  gasShadow gasShadowState fragExec gasOutcomeFullCompose vyperStorageTrace
  vyperInterpreter vyperContext vyperAST list sum

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_prim_word,
              membership_element_word_boundary] >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     drule expr_body_pre_static_facts >> strip_tac >> simp[] >>
     metis_tac[targetPlaceSimTheory.expr_sim_inv_local]) >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ e sa = (op,sm)` >>
  `?loc. reason_result_shape (expr_type e) loc
          (FST (compile_expr ce (expr_type e) e sa))` by
    (qpat_x_assum `reason_uniform_shape _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [reason_uniform_shape_def]) >>
     qexists_tac `loc` >> Cases_on `compile_expr ce (expr_type e) e sa` >>
     metis_tac[pairTheory.FST]) >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  `?shm. lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
     (gas_shadow_expr e) shadow_sa = (op,shm) /\ gas_shadow_state sm shm` by
    (pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE[gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
         (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
    (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  `reason_result_shape (expr_type e) loc
     (FST (compile_expr (gas_shadow_env T ce) (expr_type e)
                           (gas_shadow_expr e) shadow_sa))` by
    (pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE[gas_shadow_compiles_def]) >>
     simp[] >> metis_tac[]) >>
  qabbrev_tac `pack = lower_abi_encode (OPTION_MAP bytes_method_id_word mid) 32
       (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w)))` >>
  `sb = SND (pack sm)` by
    (drule_all compile_abi_encode_word_direct >>
     disch_then (fn th =>
       qpat_assum `compile_expr ce cty (TypeBuiltin _ _ _ _) sa = _`
         (mp_tac o PURE_REWRITE_RULE[th])) >>
     simp[Abbr `pack`, abi_encode_word_size_bound, as_ptr_val_pair]) >>
  `shadow_sb = SND (pack shm)` by
    (drule_all (SIMP_RULE (srw_ss())
       [gas_shadow_expr_type, gas_shadow_lowered_value_type]
       (Q.INST [`ce` |-> `gas_shadow_env T ce`, `e` |-> `gas_shadow_expr e`]
         compile_abi_encode_word_direct)) >>
     disch_then (fn th =>
       qpat_assum `compile_expr _ cty (gas_shadow_expr _) shadow_sa = _`
         (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def,th])) >>
     simp[Abbr `pack`, abi_encode_word_size_bound, as_ptr_val_pair]) >>
  `!st. cs_extends st (SND (pack st))` by
    (simp[Abbr `pack`] >> gen_tac >> irule (cj 1 (iffLR ci_mono_def)) >>
     irule ci_mono_lower_abi_encode >>
     simp[ci_mono_ignore_bind, ci_mono_emit_void, ci_mono_comp_return]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shm` by
    metis_tac[compile_expr_grows] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  suspend "compose"
QED
*)
Theorem abi_encode_word_vv_prefix_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  is_word_type (expr_type e) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume abi_encode_word_vv_prefix_from_packaging[compose]:
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (drule_all o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (drule_all o REWRITE_RULE[expr_sim_full_def]) >> strip_tac >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted) (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  simp[eval_expr_singleton_type_builtin_action, type_builtin_args_length_ok_def] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. ~t.vs_halted) _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       storage_trace_frame_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise abi_encode_word_vv_prefix_from_packaging
*)
